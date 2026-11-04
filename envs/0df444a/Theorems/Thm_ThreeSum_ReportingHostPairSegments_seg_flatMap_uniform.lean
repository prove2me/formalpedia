-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairSegments_seg_flatMap_uniform
-- name    : ThreeSum.ReportingHostPairSegments.seg_flatMap_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:23.280749+00:00
-- url     : https://prove2.me/theorems/252c7272-92e7-48b4-b8ec-249e8c639e98
-- title:
--   Reporting Host Pair Segments: seg flat Map uniform
-- statement:
--   The Reporting Host Pair Segments construction uses the seg flat Map uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L13-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean#L13-L35

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}

theorem ThreeSum.ReportingHostPairSegments.seg_flatMap_uniform {μ : ℕ → ℤ} {dst n : ℕ} (xs : List α) (f : α → List ℤ)
    (hlen : ∀ x ∈ xs, (f x).length = n)
    (hout : ∀ i (hi : i < xs.length), ∀ j (hj : j < n),
      μ (dst+i*n+j) = (f xs[i])[j]'(by rw [hlen _ (List.getElem_mem hi)]; exact hj)) :
    Seg μ dst (xs.flatMap f) := by sorry
