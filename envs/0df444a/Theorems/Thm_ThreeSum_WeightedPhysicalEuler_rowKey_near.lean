-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_near
-- name    : ThreeSum.WeightedPhysicalEuler.rowKey_near
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:11.725544+00:00
-- url     : https://prove2.me/theorems/420aeea0-a76d-4d13-a067-0c66fe5b718a
-- title:
--   Weighted Physical Euler: row Key near
-- statement:
--   The Weighted Physical Euler construction uses the row Key near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L89-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L89-L95

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

theorem ThreeSum.WeightedPhysicalEuler.rowKey_near {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : T<cacheCost (predecessor R i)) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      nv+ordinal nearWords nn (predecessor R i) := by sorry
