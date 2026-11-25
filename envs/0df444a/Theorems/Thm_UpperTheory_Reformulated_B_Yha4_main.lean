-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yha4_main
-- name    : UpperTheory.Reformulated.B.Yha4.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:23.441493+00:00
-- url     : https://prove2.me/theorems/c0935021-7abe-5737-977e-45512a2a05c8
-- title:
--   Yha4: main
-- statement:
--   The Yha4 construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FInt.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FInt.lean#L14-L28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by sorry
