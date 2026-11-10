-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball
-- name    : ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:43:58.218536+00:00
-- url     : https://prove2.me/theorems/e47c11b2-f4fd-4701-98c0-e91d24adcdc6
-- title:
--   Square integrability on a finite-measure ball
-- statement:
--   The square function is integrable on any finite-measure real ball by comparison with its clamped square.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4253-L4275

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball (r : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} m := by sorry
