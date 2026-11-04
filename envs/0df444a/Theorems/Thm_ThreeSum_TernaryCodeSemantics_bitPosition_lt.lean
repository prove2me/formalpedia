-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_bitPosition_lt
-- name    : ThreeSum.TernaryCodeSemantics.bitPosition_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:07.649197+00:00
-- url     : https://prove2.me/theorems/6f3380ba-93f4-4526-b0f7-306979d637aa
-- title:
--   Ternary Code Semantics: bit Position lt
-- statement:
--   The Ternary Code Semantics construction uses the bit Position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L42-L46

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.bitPosition_lt {N : ℕ} (p : Fin N × Fin 2) : bitPosition p<2*N := by sorry
