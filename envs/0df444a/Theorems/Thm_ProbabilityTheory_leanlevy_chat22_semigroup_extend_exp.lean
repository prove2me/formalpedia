-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_extend_exp
-- name    : ProbabilityTheory.leanlevy_chat22_semigroup_extend_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:01:42.538414+00:00
-- url     : https://prove2.me/theorems/0edb0dc3-4cad-46be-b88f-be0e097d0d86
-- title:
--   Extend a rational-time exponential semigroup by right continuity
-- statement:
--   If a complex semigroup is right continuous and agrees with a fixed complex exponential on all nonnegative rational times, it agrees with that exponential at every nonnegative time.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean charFun_eq_exp_mul phase 5, original ceiling-rational approximation.

import Mathlib
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_semigroup_extend_exp
    (φ : ℝ≥0 → ℂ) (c : ℂ)
    (hφ_right : ∀ t, Tendsto φ (𝓝[≥] t) (𝓝 (φ t)))
    (hrat_exp : ∀ (k n : ℕ), 0 < n →
      φ ((k : ℝ≥0) / (n : ℝ≥0)) = exp (c * ↑((k : ℝ) / (n : ℝ)))) :
    ∀ t : ℝ≥0, φ t = exp (c * ↑(t : ℝ)) := by sorry
