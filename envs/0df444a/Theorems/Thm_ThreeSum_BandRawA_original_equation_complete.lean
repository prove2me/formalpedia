-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_original_equation_complete
-- name    : ThreeSum.BandRawA.original_equation_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:50.149773+00:00
-- url     : https://prove2.me/theorems/effeee2d-adcf-491d-b2a8-d959672088a7
-- title:
--   Band Raw A: original equation complete
-- statement:
--   The Band Raw A construction uses the original equation complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L95-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L95-L104

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by sorry
