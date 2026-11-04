-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
-- name    : ThreeSum.TernaryCodeSemantics.digit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:17.241415+00:00
-- url     : https://prove2.me/theorems/6f33dff9-d7f7-470a-afa3-eab00b8ccc06
-- title:
--   Ternary Code Semantics: digit eq
-- statement:
--   The Ternary Code Semantics construction uses the digit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L195-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L195-L200

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.digit_eq {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.digit (2*N) (low i) (high i) (address w)=(w i).val := by sorry
