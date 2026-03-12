module
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import SpherePacking.ModularForms.Cauchylems
public import SpherePacking.ModularForms.limunder_lems
public import SpherePacking.ModularForms.tendstolems
public import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.ModularForms.SummableLemmas.Basic
import SpherePacking.ModularForms.SummableLemmas.Cotangent
import SpherePacking.ModularForms.SummableLemmas.G2
import SpherePacking.ModularForms.SummableLemmas.QExpansion
import SpherePacking.ModularForms.SummableLemmas.IntPNat

@[expose] public section

/-!
# The Eisenstein series `E₂`

This file defines the weight-2 Eisenstein series `E₂` on the upper half-plane, together with the
auxiliary series `G₂` used to define it and a correction term `D₂` which appears in its modular
transformation behavior.

## Main definitions
* `G₂`, `G₂_a`
* `E₂`
* `D₂`
-/

open scoped Interval Real Topology BigOperators Nat Matrix.SpecialLinearGroup

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory
  Metric Filter Function Complex MatrixGroups Matrix.SpecialLinearGroup

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups
open ArithmeticFunction

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma

noncomputable section

/-- Compatibility alias for Mathlib's `EisensteinSeries.G2`. -/
public def G₂ : ℍ → ℂ := EisensteinSeries.G2

/-- Compatibility alias for Mathlib's `EisensteinSeries.E2`. -/
public def E₂ : ℍ → ℂ := EisensteinSeries.E2

/-- Compatibility alias for Mathlib's `EisensteinSeries.D2`. -/
public def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma D₂_apply (γ : SL(2, ℤ)) (z : ℍ) :
    D₂ γ z = (2 * π * Complex.I * γ 1 0) / (γ 1 0 * z + γ 1 1) := by
  rfl

lemma D2_one : D₂ 1 = 0 := by
  ext z
  simp [D₂]

lemma D2_mul (A B : SL(2, ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B) := by
  simpa [D₂] using (EisensteinSeries.D2_mul A B)

lemma D2_inv (A : SL(2, ℤ)) : (D₂ A) ∣[(2 : ℤ)] A⁻¹ = -D₂ (A⁻¹) := by
  simpa [D₂] using (EisensteinSeries.D2_inv A)

lemma D2_T : D₂ ModularGroup.T = 0 := by
  simpa [D₂] using (EisensteinSeries.D2_T)

lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z := by
  simp [D₂, ModularGroup.S, ModularGroup.denom_apply]

lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
    ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
  calc
    G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
          simpa [G₂] using (EisensteinSeries.G2_eq_tsum_cexp z)
    _ = (2 * riemannZeta 2) - 8 * π ^ 2 *
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
          congr 2
          apply tsum_congr
          intro n
          rw [← Complex.exp_nat_mul]
          congr 1
          ring_nf

lemma G2_periodic : (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  simpa [G₂] using (EisensteinSeries.G2_T_transform)

lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ) := by
  simpa [G₂, D₂] using (EisensteinSeries.G2_slash_action γ)

/-- E₂ is 1-periodic: E₂(z + 1) = E₂(z). -/
lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
  rw [modular_slash_T_apply] at h
  simpa [E₂, EisensteinSeries.D2_T] using h

/-- The `S`-transform of `E₂` in slash-action form. -/
lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
    E₂ z + 6 / (π * Complex.I * z) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  have h' : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
      E₂ z - (1 / (2 * riemannZeta 2)) * (2 * π * Complex.I / z) := by
    simpa [E₂, EisensteinSeries.D2_S, smul_eq_mul] using h
  rw [riemannZeta_two] at h'
  have hpi : (π : ℂ) ≠ 0 := by simp
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  calc
    (E₂ ∣[(2 : ℤ)] ModularGroup.S) z = E₂ z - 1 / (2 * (π ^ 2 / (6 : ℂ))) * (2 * π * Complex.I / z) := h'
    _ = E₂ z + 6 / (π * Complex.I * z) := by
      field_simp [hpi, hI, hz]
      ring_nf
      simp [Complex.I_sq, add_comm]

/-- E₂ transforms under SL(2,ℤ) as: E₂ ∣[2] γ = E₂ - α • D₂ γ where α = 1/(2ζ(2)) -/
public lemma E₂_slash_transform (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ := by
  simpa [E₂, D₂] using (EisensteinSeries.E2_slash_action γ)

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)).
    This is derived from E₂_transform by relating the slash action to the direct value. -/
public lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_two] at h
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero hz hz
  have h' := congrArg (· * ((z : ℂ) * (z : ℂ))) h
  simp only at h'
  -- Cancel the `z^(-2)` factor coming from the slash action.
  rw [mul_assoc, inv_mul_cancel₀ hz2, mul_one] at h'
  simpa [sq, mul_comm, mul_left_comm, mul_assoc] using h'

/-- Convert a geometric-series expression to a divisor-sum expression via `sigma`. -/
public lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ, (n + 1) *
    cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π * Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  let q : ℂ := cexp (2 * π * Complex.I * z)
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ 1 * q ^ n / (1 - q ^ n)
  let g : ℕ → ℂ := fun n => sigma 1 n * q ^ n
  have h :
      ∑' n : ℕ+, f n = ∑' n : ℕ+, g n := by
    simpa [f, g, q] using
      (tsum_pow_div_one_sub_eq_tsum_sigma (r := q) (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1)
  have hf := tsum_pnat_eq_tsum_succ (f := f)
  have hg := tsum_pnat_eq_tsum_succ (f := g)
  rw [hf, hg] at h
  calc
    ∑' n : ℕ, (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) /
        (1 - cexp (2 * π * Complex.I * (n + 1) * z))
      = ∑' n : ℕ, f (n + 1) := by
          apply tsum_congr
          intro n
          have hpow : cexp (2 * π * Complex.I * (n + 1) * z) = q ^ (n + 1) := by
            dsimp [q]
            rw [← Complex.exp_nat_mul]
            congr 1
            have hn : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
              norm_num [Nat.cast_add]
            rw [hn]
            ring
          simp [f, pow_one, hpow]
    _ = ∑' n : ℕ, g (n + 1) := h
    _ = ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
          apply tsum_congr
          intro n
          have hpow : cexp (2 * π * Complex.I * (n + 1) * z) = q ^ (n + 1) := by
            dsimp [q]
            rw [← Complex.exp_nat_mul]
            congr 1
            have hn : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
              norm_num [Nat.cast_add]
            rw [hn]
            ring
          simp [g, hpow]

lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂, EisensteinSeries.E2]
  simp [smul_eq_mul]
  rw [EisensteinSeries.G2_eq_tsum_cexp]
  rw [mul_sub]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.pi_pos.ne')
  congr 1
  · rw [riemannZeta_two]
    field_simp [hpi]
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      have hpi : (π : ℂ) ≠ 0 := by simp
      grind
    · calc
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ)
            = ∑' n : ℕ+, (n : ℂ) ^ 1 * cexp (2 * π * Complex.I * z) ^ (n : ℕ) /
                (1 - cexp (2 * π * Complex.I * z) ^ (n : ℕ)) := by
                  simpa [pow_one] using
                    (tsum_pow_div_one_sub_eq_tsum_sigma
                      (r := cexp (2 * π * Complex.I * z))
                        (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1).symm
        _ = ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
            (1 - cexp (2 * π * Complex.I * n * z)) := by
              apply tsum_congr
              intro n
              have hpow : cexp (2 * π * Complex.I * n * z) =
                  cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
                rw [← Complex.exp_nat_mul]
                congr 1
                ring
              simp [pow_one, hpow]

