-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogSelection_selected_leaf
-- name    : ThreeSum.ReportingHostCatalogSelection.selected_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:12.442315+00:00
-- url     : https://prove2.me/theorems/7a27b6b7-85dd-468c-b00c-8f3289d81873
-- title:
--   Reporting Host Catalog Selection: selected leaf
-- statement:
--   The Reporting Host Catalog Selection construction uses the selected leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L32-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L32-L43

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogSelection
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostCatalogSelection.selected_leaf {h J k i : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre)) :
    leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i) =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre := by sorry
