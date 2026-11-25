-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r25a_sq_sub_one_lower_bound
-- name    : UpperTheory.Reformulated.B.P6.r25a.sq_sub_one_lower_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:25.843705+00:00
-- url     : https://prove2.me/theorems/13e6d49d-c9e6-593c-a6d9-41508e3c0d30
-- title:
--   r25a: sq sub one lower bound
-- statement:
--   The r25a construction uses the sq sub one lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r25a

theorem UpperTheory.Reformulated.B.P6.r25a.sq_sub_one_lower_bound (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by sorry
