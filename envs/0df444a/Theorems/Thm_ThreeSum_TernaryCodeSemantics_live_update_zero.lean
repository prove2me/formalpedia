-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_live_update_zero
-- name    : ThreeSum.TernaryCodeSemantics.live_update_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:02.071674+00:00
-- url     : https://prove2.me/theorems/5bcd1b54-9033-4ab3-b2ef-c150cae7afcd
-- title:
--   Ternary Code Semantics: live update zero
-- statement:
--   The Ternary Code Semantics construction uses the live update zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L100-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L100-L107

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.live_update_zero {N : ℕ} (w : TritWord N) (i : Fin N)
    (p : Fin N × Fin 2) :
    live (Function.update w i 0) p ↔ live w p ∧ p≠(i,0) ∧ p≠(i,1) := by sorry
