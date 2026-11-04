-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_oneCode_eq_update_of_pos
-- name    : ThreeSum.TernaryCodeSemantics.oneCode_eq_update_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:08.892099+00:00
-- url     : https://prove2.me/theorems/a99f67fc-eaf0-4f9b-8bbc-77b2a92551bd
-- title:
--   Ternary Code Semantics: one Code eq update of pos
-- statement:
--   The Ternary Code Semantics construction uses the one Code eq update of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L222-L227
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L222-L227

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.oneCode_eq_update_of_pos {N : ℕ} (w : TritWord N) (i : Fin N)
    (h : 0<(w i).val) :
    LightTernaryCodes.oneCode (2*N) (high i) (address w)=
      address (Function.update w i 1) := by sorry
