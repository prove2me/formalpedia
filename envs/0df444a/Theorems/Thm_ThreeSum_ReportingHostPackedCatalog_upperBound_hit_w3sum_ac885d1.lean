-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_upperBound_hit_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostPackedCatalog.upperBound_hit_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:48.336952+00:00
-- url     : https://prove2.me/theorems/a168c2d4-6ef2-4c5b-ae55-b685b4a83a48
-- title:
--   Reporting Host Packed Catalog: upper Bound hit
-- statement:
--   The Reporting Host Packed Catalog construction uses the upper Bound hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L75-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L75-L118

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.upperBound_hit_w3sum_ac885d1 {key : ℕ → ℕ} {n i : ℕ} {S : List ℤ}
    (hi : i < n) (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hperm : S.Perm (codes key n)) (hs : S.Pairwise (· ≤ ·)) :
    let K := BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)
    0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (packed key n i : ℤ) := by sorry
