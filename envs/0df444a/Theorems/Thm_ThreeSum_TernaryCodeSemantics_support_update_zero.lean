-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_update_zero
-- name    : ThreeSum.TernaryCodeSemantics.support_update_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:36.850267+00:00
-- url     : https://prove2.me/theorems/764e100b-a386-4218-a356-ee766c64c659
-- title:
--   Ternary Code Semantics: support update zero
-- statement:
--   The Ternary Code Semantics construction uses the support update zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L132-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L132-L137

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

theorem ThreeSum.TernaryCodeSemantics.support_update_zero {N : ℕ} (w : TritWord N) (i : Fin N) :
    support (Function.update w i 0)=((support w).erase (high i)).erase (low i) := by sorry
