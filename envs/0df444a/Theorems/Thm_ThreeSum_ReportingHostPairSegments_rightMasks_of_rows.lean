-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairSegments_rightMasks_of_rows
-- name    : ThreeSum.ReportingHostPairSegments.rightMasks_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:12.21893+00:00
-- url     : https://prove2.me/theorems/631f120f-19fa-42cc-9896-b2aaec71616e
-- title:
--   Reporting Host Pair Segments: right Masks of rows
-- statement:
--   The Reporting Host Pair Segments construction uses the right Masks of rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L73-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L73-L86

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}

theorem ThreeSum.ReportingHostPairSegments.rightMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (rightAt L h i j) : ℤ)) :
    Seg μ dst (rightMasks L h) := by sorry
