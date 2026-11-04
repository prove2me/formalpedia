-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_zero
-- name    : ThreeSum.WeightedPhysicalEuler.rowKey_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:57.263168+00:00
-- url     : https://prove2.me/theorems/e7967420-4c93-4802-893d-e208ec170ee4
-- title:
--   Weighted Physical Euler: row Key zero
-- statement:
--   The Weighted Physical Euler construction uses the row Key zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L76-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L76-L79

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedPhysicalEuler.rowKey_zero {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : (R i).val=0) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=bv := by sorry
