-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairSegments_leftMasks_of_rows
-- name    : ThreeSum.ReportingHostPairSegments.leftMasks_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:22.206586+00:00
-- url     : https://prove2.me/theorems/1e3ab68b-f9ee-4a7b-95af-b4735e31221d
-- title:
--   Reporting Host Pair Segments: left Masks of rows
-- statement:
--   The Reporting Host Pair Segments construction uses the left Masks of rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L58-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L58-L71

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}

theorem ThreeSum.ReportingHostPairSegments.leftMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (leftAt L h i) : ℤ)) :
    Seg μ dst (leftMasks L h) := by sorry
