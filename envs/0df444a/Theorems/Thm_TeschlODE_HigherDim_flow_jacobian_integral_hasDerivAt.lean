-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_flow_jacobian_integral_hasDerivAt
-- name    : TeschlODE.HigherDim.flow_jacobian_integral_hasDerivAt
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-07T00:34:06.28357+00:00
-- url     : https://prove2.me/theorems/3dfcc77b-bbbd-4579-b95e-39ed5d4a1217
-- title:
--   Integrated Jacobian evolution of a C1 flow
-- statement:
--   For a globally C1 vector field and a bounded open set whose closure is alive at time t0, the integral over the initial set of the absolute determinant of the spatial flow derivative has derivative equal to the integral of the absolute determinant times divergence along the flow. This is the integrated form of the variational equation and Jacobi identity, before identifying the integral with image volume.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems, Lemma 8.8, p. 236 (8.28), proof on p. 237; auxiliary step for volume_hasDerivAt.

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_divergence

open MeasureTheory Set

set_option autoImplicit false

theorem TeschlODE.HigherDim.flow_jacobian_integral_hasDerivAt {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    HasDerivAt
      (fun t : ℝ => ∫ x in U, |(fderiv ℝ (Φ t) x).det|)
      (∫ x in U, |(fderiv ℝ (Φ t₀) x).det| * divergence f (Φ t₀ x)) t₀ := by sorry
