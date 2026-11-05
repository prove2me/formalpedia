-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_zero
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.rowKey_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:47.753201+00:00
-- url     : https://prove2.me/theorems/ec67f84d-8fa5-484d-b1c8-4723c2dd48dd
-- title:
--   rowKey_zero
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L76-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L76-L79

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.rowKey_zero {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : (R i).val=0) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=bv := by sorry
