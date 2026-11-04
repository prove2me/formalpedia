-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_primitive_bounds
-- name    : ThreeSum.SharedReportingBankResourceBounds.primitive_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:25:43.197079+00:00
-- url     : https://prove2.me/theorems/a8f5e87b-5286-408c-b73e-6d4e09bcb8cf
-- title:
--   Shared Reporting Bank Resource Bounds: primitive bounds
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the primitive bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L40-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean#L40-L50

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.primitive_bounds (n : ℕ) :
    half n ≤ inputBits n ∧ blocks n ≤ 20*inputBits n ∧
    2*half n*blocks n ≤ inputBits n ∧
    width (half n) (blocks n) ≤ 256*inputBits n := by sorry
