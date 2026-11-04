-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_lower_bound
-- name    : ThreeSum.WeightedPhysicalEuler.rowKey_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:51.532004+00:00
-- url     : https://prove2.me/theorems/5bb215b0-d997-4aa4-a9ab-cd61cfe75699
-- title:
--   Weighted Physical Euler: row Key lower bound
-- statement:
--   The Weighted Physical Euler construction uses the row Key lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L170-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L170-L176

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

theorem ThreeSum.WeightedPhysicalEuler.rowKey_lower_bound {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv≤nv) (i : Fin N) :
    bv≤rowKey R bankWords nearWords nb nn T bv nv i.val := by sorry
