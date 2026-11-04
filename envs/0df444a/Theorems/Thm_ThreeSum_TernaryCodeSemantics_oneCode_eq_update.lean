-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_oneCode_eq_update
-- name    : ThreeSum.TernaryCodeSemantics.oneCode_eq_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:44.678776+00:00
-- url     : https://prove2.me/theorems/9a559fa4-fd13-4ad4-bb4e-a9401709975a
-- title:
--   Ternary Code Semantics: one Code eq update
-- statement:
--   The Ternary Code Semantics construction uses the one Code eq update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L153-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L153-L158

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

theorem ThreeSum.TernaryCodeSemantics.oneCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.oneCode (2*N) (high i) (address w) =
      address (Function.update w i (clampOne (w i))) := by sorry
