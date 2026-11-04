-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_linear_le_magnitude
-- name    : ThreeSum.SharedReportingBankResourceBounds.linear_le_magnitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:25:32.077083+00:00
-- url     : https://prove2.me/theorems/257a0943-0909-4270-ad8a-2eebfc99a3dc
-- title:
--   Shared Reporting Bank Resource Bounds: linear le magnitude
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the linear le magnitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L52-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L52-L57

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.linear_le_magnitude (n : ℕ) : 2048*(inputBits n+1) ≤ magnitude n := by sorry
