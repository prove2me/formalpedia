-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_update_one
-- name    : ThreeSum.TernaryCodeSemantics.support_update_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:44.305026+00:00
-- url     : https://prove2.me/theorems/a70667ff-79eb-4d23-9b49-1fca7a65fdfd
-- title:
--   Ternary Code Semantics: support update one
-- statement:
--   The Ternary Code Semantics construction uses the support update one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L139-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L139-L143

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

theorem ThreeSum.TernaryCodeSemantics.support_update_one {N : ℕ} (w : TritWord N) (i : Fin N) :
    support (Function.update w i (clampOne (w i)))=(support w).erase (high i) := by sorry
