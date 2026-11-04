-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_eq_sum
-- name    : ThreeSum.TernaryCodeSemantics.address_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:14.380332+00:00
-- url     : https://prove2.me/theorems/a5d6e51a-f65f-4d74-a39b-7f2ccd44c06e
-- title:
--   Ternary Code Semantics: address eq sum
-- statement:
--   The Ternary Code Semantics construction uses the address eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L53-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L53-L67

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.address_eq_sum {N : ℕ} (w : TritWord N) :
    address w=∑ i, digitCode (w i).val*4^(N-1-i.val) := by sorry
