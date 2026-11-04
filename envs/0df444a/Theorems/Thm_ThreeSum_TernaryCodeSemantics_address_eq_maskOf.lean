-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_eq_maskOf
-- name    : ThreeSum.TernaryCodeSemantics.address_eq_maskOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:59.227208+00:00
-- url     : https://prove2.me/theorems/8bc8763b-7abe-46ac-be80-ef1fa644cea5
-- title:
--   Ternary Code Semantics: address eq mask Of
-- statement:
--   The Ternary Code Semantics construction uses the address eq mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L69-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L69-L85

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.address_eq_maskOf {N : ℕ} (w : TritWord N) : address w=maskOf (support w) := by sorry
