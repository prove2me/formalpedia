-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_low_lt
-- name    : ThreeSum.TernaryCodeSemantics.low_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:59.632496+00:00
-- url     : https://prove2.me/theorems/8cd60451-8603-4695-83a7-1dafc5d62ec3
-- title:
--   Ternary Code Semantics: low lt
-- statement:
--   The Ternary Code Semantics construction uses the low lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L202-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L202-L203

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.low_lt {N : ℕ} (i : Fin N) : low i<2*N := by sorry
