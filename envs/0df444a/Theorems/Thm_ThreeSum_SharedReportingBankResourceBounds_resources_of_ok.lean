-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_resources_of_ok
-- name    : ThreeSum.SharedReportingBankResourceBounds.resources_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:30:58.381011+00:00
-- url     : https://prove2.me/theorems/7ed6096e-0819-4c85-b330-879d14b07bbe
-- title:
--   Shared Reporting Bank Resource Bounds: resources of ok
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the resources of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsPolynomial.lean#L74-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsPolynomial.lean#L74-L78

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section

theorem ThreeSum.SharedReportingBankResourceBounds.resources_of_ok {lim : Light.Limits} {n U free NB NC d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n) (hok : (need n U).Ok lim free d) :
    LightSharedReportingHost.Resources lim free (half n) (blocks n)
      NB NC (BandScales.bandSize n) d := by sorry
