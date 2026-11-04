-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_predCost_canonical
-- name    : ThreeSum.WeightedPhysicalEuler.predCost_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:53.603917+00:00
-- url     : https://prove2.me/theorems/7929bf26-f6ba-409f-a7b7-31ddbc7ad12e
-- title:
--   Weighted Physical Euler: pred Cost canonical
-- statement:
--   The Weighted Physical Euler construction uses the pred Cost canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L53-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L53-L59

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_predCost_canonical

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedPhysicalEuler.predCost_canonical {N : ℕ} (R : TritWord N) (i : Fin N) (hi : 0<(R i).val) :
    LightWeightedPredecessor.predCost N (LightWeightedEulerMetadata.lowAt N i.val)
      (LightWeightedEulerMetadata.highAt N i.val) (address R)=cacheCost (predecessor R i) := by sorry
