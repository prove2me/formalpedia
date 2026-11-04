-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_color_power_le
-- name    : ThreeSum.LightBandRawAResources.color_power_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:34:22.404002+00:00
-- url     : https://prove2.me/theorems/7fcfbb21-0fd1-4cfa-8537-10baafab32f3
-- title:
--   Light Band Raw AResources: color power le
-- statement:
--   The Light Band Raw AResources construction uses the color power le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResourcesScales.lean#L34-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResourcesScales.lean#L34-L42

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.color_power_le (n : ℕ) : 2^((inputBits n+1)+1) ≤ 4*(n+1) := by sorry
