-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_keep_w3sum_ac885d1
-- name    : ThreeSum.SourceFiniteData.Normalized.keep_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:59:57.018018+00:00
-- url     : https://prove2.me/theorems/e0e0054f-c42a-4a65-8bfb-bcea3b66df2e
-- title:
--   Normalized: keep
-- statement:
--   The Normalized construction uses the keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteRetention.lean#L9-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteRetention.lean#L9-L53

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Definitions.Def_WeightedCache3SUM_Alias_a6ca635f54b46105
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light BandPartition BandCandidateRows BandRawA

theorem ThreeSum.SourceFiniteData.Normalized.keep_w3sum_ac885d1 {μ ν : ℕ → ℤ} {av ae bv be cv ce tables rec vals g n bound : ℕ}
    {hg : 0 < g} {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r)
    (hk : Kept μ ν bound)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ bound) (hae : ae+2+2*n ≤ bound)
    (hbv : bv+n ≤ bound) (hbe : be+2+2*n ≤ bound)
    (hcv : cv+n ≤ bound) (hce : ce+2+2*n ≤ bound)
    (htables : tables+ColorBandBounds.count n g ≤ bound)
    (hrecords : rec+4*ColorBandBounds.count n g ≤ bound)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n g) g ≤ bound) :
    Normalized ν av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := by sorry
