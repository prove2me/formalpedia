-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_nonnegative_iff_shell_and_cross_budget
-- name    : WeilDefect.MarkerStability.nonnegative_iff_shell_and_cross_budget
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:11:35.060833+00:00
-- url     : https://prove2.me/theorems/823b7d37-9893-4166-99b9-21a4f24016b5
-- title:
--   Positive core reduces full operator positivity to shell positivity and a relative coupling bound
-- statement:
--   Let $A$ be a bounded self-adjoint operator on a complex Hilbert space $K$, and let $U:H\to K$ be a linear isometry from a complex Hilbert space. Write $q(v)=\operatorname{Re}\langle Av,v\rangle$, and suppose $q(Ux)\ge0$ for every $x\in H$. Then $$A\ge0\iff\left[\begin{array}{l}q(z)\ge0\quad\text{for every }z\in\ker U^*,\\ |\langle AUx,z\rangle|^2\le q(Ux)q(z)\quad\text{for every }x\in H,\ z\in\ker U^*.\end{array}\right]$$ No invertibility or positive spectral gap is required on the core. The companion native Connes development applies this to the unchanged original relative covariance and constructed original support inclusion, isolating the exact two remaining shell estimates at the certified inner cut. Those arithmetic estimates and the endpoint half-bound are not asserted here.
-- source:
--   monocap-tech/weil, Screening/RelativeShell.lean, with actual original-actor endpoint reduction in Connes/RelativeShellEndpoint.lean. Complete private positive-form Cauchy-Schwarz and quadratic-expansion lemmas are included for independent checking. This generic Hilbert-space support theorem is applied to the original physical carrier; it does not replace actual zeros or their original actors by a surrogate.

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem nonnegative_operator_pair_cauchy_schwarz (A : K →L[ℂ] K) (hA : 0 ≤ A)
    (u z : K) :
    ‖⟪A u, z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪A u, u⟫_ℂ * RCLike.re ⟪A z, z⟫_ℂ := by
  let B := CFC.sqrt A
  have hB : B.adjoint = B := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hBB : B ∘L B = A := CFC.sqrt_mul_sqrt_self A hA
  have he : ∀ x : K, ‖B x‖ ^ 2 = RCLike.re ⟪A x, x⟫_ℂ := by
    intro x
    have h := B.adjoint.apply_norm_sq_eq_inner_adjoint_left x
    simpa only [hB, ← ContinuousLinearMap.comp_apply, hBB] using h
  have hi : ⟪A u, z⟫_ℂ = ⟪B u, B z⟫_ℂ := by
    calc
      _ = ⟪B.adjoint (B u), z⟫_ℂ := by rw [hB, ← ContinuousLinearMap.comp_apply, hBB]
      _ = _ := B.adjoint_inner_left z (B u)
  have hb := pow_le_pow_left₀ (norm_nonneg (⟪B u, B z⟫_ℂ)) (norm_inner_le_norm (𝕜 := ℂ) (B u) (B z)) 2
  calc
    _ = ‖⟪B u, B z⟫_ℂ‖ ^ 2 := congrArg (fun w : ℂ => ‖w‖ ^ 2) hi
    _ ≤ (‖B u‖ * ‖B z‖) ^ 2 := hb
    _ = _ := by rw [mul_pow, he u, he z]

/-- Exact real quadratic expansion with its original self-adjoint cross term. -/
private theorem selfAdjoint_quadratic_add (A : K →L[ℂ] K) (hA : IsSelfAdjoint A) (u z : K) :
    RCLike.re ⟪A (u + z), u + z⟫_ℂ =
      RCLike.re ⟪A u, u⟫_ℂ + 2 * RCLike.re ⟪A u, z⟫_ℂ + RCLike.re ⟪A z, z⟫_ℂ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hc : RCLike.re ⟪A z, u⟫_ℂ = RCLike.re ⟪A u, z⟫_ℂ := by
    exact (congrArg (fun w : ℂ => RCLike.re w) (hs z u)).trans (inner_re_symm z (A u))
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hc]
  ring

theorem WeilDefect.MarkerStability.nonnegative_iff_shell_and_cross_budget (A : K →L[ℂ] K)
    (hA : IsSelfAdjoint A) (U : H →ₗᵢ[ℂ] K)
    (hcore : ∀ x : H, 0 ≤ RCLike.re ⟪A (U x), U x⟫_ℂ) :
    0 ≤ A ↔
    (∀ z : K, U.toContinuousLinearMap.adjoint z = 0 → 0 ≤ RCLike.re ⟪A z, z⟫_ℂ) ∧
    (∀ x : H, ∀ z : K, U.toContinuousLinearMap.adjoint z = 0 →
      ‖⟪A (U x), z⟫_ℂ‖ ^ 2 ≤
        RCLike.re ⟪A (U x), U x⟫_ℂ * RCLike.re ⟪A z, z⟫_ℂ) := by sorry
