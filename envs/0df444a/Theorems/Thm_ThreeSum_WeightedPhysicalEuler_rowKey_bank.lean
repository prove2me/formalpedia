-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_bank
-- name    : ThreeSum.WeightedPhysicalEuler.rowKey_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:27.992516+00:00
-- url     : https://prove2.me/theorems/7a3ddd46-d600-463c-96cf-a9c0d2185cc0
-- title:
--   Weighted Physical Euler: row Key bank
-- statement:
--   The Weighted Physical Euler construction uses the row Key bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L81-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L81-L87

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

theorem ThreeSum.WeightedPhysicalEuler.rowKey_bank {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : cacheCost (predecessor R i)≤T) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      bv+ordinal bankWords nb (predecessor R i) := by sorry
