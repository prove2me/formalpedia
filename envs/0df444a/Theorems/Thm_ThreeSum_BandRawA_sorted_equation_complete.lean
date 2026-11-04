-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sorted_equation_complete
-- name    : ThreeSum.BandRawA.sorted_equation_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:49.750777+00:00
-- url     : https://prove2.me/theorems/5ca143e2-090b-4e54-b096-dc944df3bc21
-- title:
--   Band Raw A: sorted equation complete
-- statement:
--   The Band Raw A construction uses the sorted equation complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L53-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L53-L93

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sorted_equation_complete {A B C : List ℤ} {g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by sorry
