-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:26:52.733025+00:00
-- url     : https://prove2.me/theorems/e71cd457-8918-4a1d-999f-2089dc7f6603
-- title:
--   Shared Reporting Bank Resource Bounds: source span le magnitude
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the source span le magnitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L113-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L113-L154

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude_w3sum_ac885d1 (n : ℕ) :
    SourceBandBankLayout.span (half n) (blocks n) (2*half n*blocks n) ≤ 100*(magnitude n+1)^3 := by sorry
