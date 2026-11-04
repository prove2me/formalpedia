-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_lowerCode_eq_update
-- name    : ThreeSum.TernaryCodeSemantics.lowerCode_eq_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:09.220389+00:00
-- url     : https://prove2.me/theorems/d2f935d6-c26b-4e26-a322-ef42a888896c
-- title:
--   Ternary Code Semantics: lower Code eq update
-- statement:
--   Every metadata code actually read by a coordinate stage is the true lower word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L235-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L235-L253

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.lowerCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤w i) : lowerCode w i d=address (Function.update w i d) := by sorry
