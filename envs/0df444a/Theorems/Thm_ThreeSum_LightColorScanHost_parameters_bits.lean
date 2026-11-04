-- Prove2me | Theorems.Thm_ThreeSum_LightColorScanHost_parameters_bits
-- name    : ThreeSum.LightColorScanHost.parameters_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:35:34.053406+00:00
-- url     : https://prove2.me/theorems/9ff192d7-34b1-42ac-b581-f49de1c7c03c
-- title:
--   Light Color Scan Host: parameters bits
-- statement:
--   The Light Color Scan Host construction uses the parameters bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorScanHost.lean#L23-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorScanHost.lean#L23-L26

import Definitions.Def_Submission_ThreeSum_LightColorScan
import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorScanHost
open Light ColorParameters LightColorParametersCosts
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.LightColorScanHost.parameters_bits {n params : ℕ} {μ : ℕ → ℤ}
    (H : Seg μ params (LightParameterInit.values n)) : μ params=(Scales.inputBits n : ℤ) := by sorry
