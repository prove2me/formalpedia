-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_zeroCode_eq_update
-- name    : ThreeSum.TernaryCodeSemantics.zeroCode_eq_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:22.104353+00:00
-- url     : https://prove2.me/theorems/6c7a944f-b75b-4a1b-b67e-634482d6bac8
-- title:
--   Ternary Code Semantics: zero Code eq update
-- statement:
--   The Ternary Code Semantics construction uses the zero Code eq update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L145-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L145-L151

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.zeroCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address w) =
      address (Function.update w i 0) := by sorry
