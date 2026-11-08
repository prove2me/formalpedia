-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_slope
-- name    : ProbabilityTheory.leanlevy_chat22_semigroup_log_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:04:43.621141+00:00
-- url     : https://prove2.me/theorems/5487421b-1139-437d-8a2e-bdfc113d1655
-- title:
--   Recover the exponential exponent as the zero-time logarithmic slope
-- statement:
--   The right-hand zero-time principal-logarithm slope of a complex exponential semigroup equals its complex exponent.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean charFun_eq_exp_mul phase 6, original branch-safe logarithm limit.

import Mathlib
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_semigroup_log_slope
    (φ : ℝ≥0 → ℂ) (c : ℂ)
    (hext : ∀ t : ℝ≥0, φ t = exp (c * ↑(t : ℝ))) :
    Filter.limUnder (𝓝[>] (0 : ℝ≥0))
      (fun t : ℝ≥0 => log (φ t) / ↑(t : ℝ)) = c := by sorry
