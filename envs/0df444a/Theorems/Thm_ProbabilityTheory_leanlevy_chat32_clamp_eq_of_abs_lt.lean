-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_clamp_eq_of_abs_lt
-- name    : ProbabilityTheory.leanlevy_chat32_clamp_eq_of_abs_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:42:08.856972+00:00
-- url     : https://prove2.me/theorems/53e44d61-5c8a-4131-830a-e6a029a487cc
-- title:
--   Clamping fixes points inside the open radius
-- statement:
--   Clamping fixes points inside the open radius
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4118-L4121

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_clamp_eq_of_abs_lt {r x : ℝ} (hx : |x| < r) : max (-r) (min x r) = x := by sorry
