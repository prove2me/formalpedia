-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositive_parentWork_le
-- name    : ThreeSum.ReportingHostPositive.parentWork_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:03.452204+00:00
-- url     : https://prove2.me/theorems/0377923e-7f85-4930-b0f6-c816c1d0ef45
-- title:
--   Reporting Host Positive: parent Work le
-- statement:
--   The Reporting Host Positive construction uses the parent Work le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L89-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L89-L96

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPositive.parentWork_le {h J k t : ℕ} (I : Finset (RawItem h J α β γ)) (hk : k < J)
    (ht : t ≤ LightBlockQuery.residualSize h J (k+1)+1) :
    parentWork I k t ≤ I.card*
      (25000*(LightBlockQuery.width h J+1)^3*
        (LightSparseQuery.queryItems (LightBlockQuery.residualSize h J (k+1)) t+1)*(groupSize h+1)) := by sorry
