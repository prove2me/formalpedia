-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_bitPosition_injective
-- name    : ThreeSum.TernaryCodeSemantics.bitPosition_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:56.841791+00:00
-- url     : https://prove2.me/theorems/368c1b36-7c07-499c-b0b3-408a2f1789ac
-- title:
--   Ternary Code Semantics: bit Position injective
-- statement:
--   The Ternary Code Semantics construction uses the bit Position injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L31-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L31-L40

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.bitPosition_injective (N : ℕ) : Function.Injective (@bitPosition N) := by sorry
