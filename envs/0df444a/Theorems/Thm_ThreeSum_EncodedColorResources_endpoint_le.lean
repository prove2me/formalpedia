-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_endpoint_le
-- name    : ThreeSum.EncodedColorResources.endpoint_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:06.493777+00:00
-- url     : https://prove2.me/theorems/42a40863-783f-4f66-9108-7300d739d94a
-- title:
--   Encoded Color Resources: endpoint le
-- statement:
--   The Encoded Color Resources construction uses the endpoint le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L66-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L66-L69

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem ThreeSum.EncodedColorResources.endpoint_le (n : ℕ) : LightBlockSourceBuild.endpointBound (half n) (blocks n) ≤ (scale n)^2 := by sorry
