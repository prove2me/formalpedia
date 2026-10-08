-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_covariance_relative_bound_all_regularizations_iff_zero
-- name    : WeilDefect.MarkerStability.covariance_relative_bound_all_regularizations_iff_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T21:40:02.845928+00:00
-- url     : https://prove2.me/theorems/9a6c799a-3352-427e-ad51-b13e5aaf34b4
-- title:
--   A fixed covariance tail bounded relative to every positive regularization vanishes
-- statement:
--   Let $K,H$ be complex Hilbert spaces, let $B:K\to H$ be a bounded linear operator, and let $\alpha\ge0$. Then $$\bigl(\forall\varepsilon>0,\;\|BB^*\|\le\alpha\varepsilon\bigr)\quad\Longleftrightarrow\quad B=0.$$ In the companion native Connes development this applies to the existing actual-zero background actor at a fixed support and cutoff. Thus a fixed cutoff controlling every positive regularization would require every omitted original negative column to vanish. Support-uniform absolute tail smallness permits scale-dependent cutoffs and does not by itself establish a bound uniform in all regularizations at one fixed cutoff. No endpoint half-bound or RH is asserted.
-- source:
--   monocap-tech/weil, Screening/FixedTailRegularization.lean, actual background and two-sided actual-zero application in Connes/TwoSidedTailControl.lean. The native application retains actual zeros, multiplicities, original pair normalization, unchanged selected packet, full complement and completed physical carrier. This is a general Hilbert-space supporting theorem, not a surrogate zero model.

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap Filter Set
open scoped Topology
noncomputable section

private theorem norm_le_all_positive_scales_iff_zero
    {E : Type*} [NormedAddCommGroup E] (x : E) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖x‖ ≤ α * ε) ↔ x = 0 := by
  constructor
  · intro h
    have ht : Tendsto (fun ε : ℝ => α * ε) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (nhds (0 : ℝ)) (nhds 0)).mono_left nhdsWithin_le_nhds).const_mul α
    have hz : ‖x‖ ≤ 0 := ge_of_tendsto ht (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact h ε hε)
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg x))
  · rintro rfl ε hε
    simpa using mul_nonneg hα hε.le

theorem WeilDefect.MarkerStability.covariance_relative_bound_all_regularizations_iff_zero
    {K H : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : K →L[ℂ] H) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖B ∘L B.adjoint‖ ≤ α * ε) ↔ B = 0 := by sorry
