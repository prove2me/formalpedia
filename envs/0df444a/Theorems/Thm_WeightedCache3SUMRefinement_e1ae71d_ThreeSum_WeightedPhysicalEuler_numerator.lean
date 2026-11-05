-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_numerator
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:44.292829+00:00
-- url     : https://prove2.me/theorems/2bcfa30e-acad-42f1-937e-381a43567dea
-- title:
--   numerator
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L115-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L115-L137

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.numerator {N nb nn T bv nv h : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (f : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (hcut : h≤rank R)
    (hsep : bv+nb≤nv)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<cacheCost (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i) :
    LightTernaryWeightedSum.sum (rowWeight R) (rowKey R bankWords nearWords nb nn T bv nv)
      (physicalValue (binomialZeta f) bankWords nearWords bv nv) N=
      (rank R-h : ℕ)*binomialZeta f R := by sorry
