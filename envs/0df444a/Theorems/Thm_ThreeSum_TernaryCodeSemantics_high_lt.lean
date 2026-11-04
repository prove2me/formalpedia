-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_high_lt
-- name    : ThreeSum.TernaryCodeSemantics.high_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:54.683172+00:00
-- url     : https://prove2.me/theorems/147bcc65-9fd3-417f-82be-b9bc1a631f43
-- title:
--   Ternary Code Semantics: high lt
-- statement:
--   The Ternary Code Semantics construction uses the high lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L205-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L205-L206

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.high_lt {N : ℕ} (i : Fin N) : high i<2*N := by sorry
