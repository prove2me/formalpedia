-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_flow_spatial_c1_on_compact
-- name    : TeschlODE.HigherDim.flow_spatial_c1_on_compact
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-07T00:34:09.210098+00:00
-- url     : https://prove2.me/theorems/210d24e1-b029-4bd4-8d33-718f9c06e0b3
-- title:
--   Spatial C1 regularity on a compact living set
-- statement:
--   For a globally C1 vector field, a bounded open set whose closure is alive at time t0 has a common open interval of lifetimes around t0. Each flow time slice is continuous on the closure and differentiable at every point of the open set.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems, Lemma 8.8, p. 236 (8.28), proof on p. 237; auxiliary step for volume_hasDerivAt.

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_divergence

open MeasureTheory Set

set_option autoImplicit false

theorem TeschlODE.HigherDim.flow_spatial_c1_on_compact {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      (∀ x ∈ closure U, t ∈ I x) ∧
      ContinuousOn (Φ t) (closure U) ∧
      ∀ x ∈ U, DifferentiableAt ℝ (Φ t) x := by sorry
