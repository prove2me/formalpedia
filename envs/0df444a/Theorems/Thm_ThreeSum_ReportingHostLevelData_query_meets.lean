-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostLevelData_query_meets
-- name    : ThreeSum.ReportingHostLevelData.query_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:57:42.290686+00:00
-- url     : https://prove2.me/theorems/2d0e2ba2-1d6d-4ed3-856b-35f54a6efb96
-- title:
--   Reporting Host Level Data: query meets
-- statement:
--   The Reporting Host Level Data construction uses the query meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L109-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean#L109-L131

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostLevelData
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostLevelData.query_meets {lim : Limits} {μ : ℕ→ℤ} {h J k baseL baseR maskBase work depth : ℕ}
    {D : Catalog} (hk : k≤J) (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D hk pMod shift B C b c w.2.2)
    (HB : Bounds h J k D baseL baseR maskBase)
    (HW : Scratch lim h J k D B.card C.card maskBase work)
    (hd : depth+2*width h J+12≤lim.depth) :
    Meets lim LightReportingCatalogQuery.program 35 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        D.t,baseL,baseR,D.boxCut,D.indexBase,D.ptrBase,count h k,maskBase,work]
      μ (LightReportingCatalogQuery.time h J k D.t)
      (fun r ν => r=(prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ ν work maskBase (LightSparseQuery.queryItems (residualSize h J k) D.t)) := by sorry
