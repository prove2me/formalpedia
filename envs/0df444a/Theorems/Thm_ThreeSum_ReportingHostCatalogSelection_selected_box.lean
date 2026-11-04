-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogSelection_selected_box
-- name    : ThreeSum.ReportingHostCatalogSelection.selected_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:31.205404+00:00
-- url     : https://prove2.me/theorems/be9e3ee5-8cbf-4bd4-9de5-80614c3217f5
-- title:
--   Reporting Host Catalog Selection: selected box
-- statement:
--   The Reporting Host Catalog Selection construction uses the selected box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L45-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogSelection.lean#L45-L61

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

theorem ThreeSum.ReportingHostCatalogSelection.selected_box {μ : ℕ → ℤ} {h J k i boxCut boxBase : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hi : i < count h k)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (hboxes : ∀ j < count h k, LightBoxStages.StoredThrough μ
      (boxBase+j*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
        (suffixStage J (512*h) k) (preL h J k j) (preR h J k j))
      (suffixStage J (512*h) k)) :
    LightBoxStages.StoredThrough μ (boxBase+i*stride (suffixStage J (512*h) k) boxCut)
      boxCut (LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre)
      (suffixStage J (512*h) k) := by sorry
