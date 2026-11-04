-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFilter_selected_nodup
-- name    : ThreeSum.LightReportingFilter.selected_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:21.021443+00:00
-- url     : https://prove2.me/theorems/b381b33f-27d7-4197-8ae1-048e60ae6612
-- title:
--   Light Reporting Filter: selected nodup
-- statement:
--   The Light Reporting Filter construction uses the selected nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L38-L39

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingFilter.selected_nodup (count : ℕ → ℕ) (j : ℕ) : (selected count j).Nodup := by sorry
