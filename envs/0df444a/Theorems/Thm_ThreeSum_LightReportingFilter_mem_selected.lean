-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
-- name    : ThreeSum.LightReportingFilter.mem_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:21.911916+00:00
-- url     : https://prove2.me/theorems/1ec1fc47-04f6-4150-9573-73ab12edae25
-- title:
--   Light Reporting Filter: mem selected
-- statement:
--   The Light Reporting Filter construction uses the mem selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L34-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L34-L36

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingFilter.mem_selected (count : ℕ → ℕ) (j i : ℕ) :
    i ∈ selected count j ↔ i < j ∧ 0 < count i := by sorry
