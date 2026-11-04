-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
-- name    : ThreeSum.TernaryEntropyRates.actual_output_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:36.413424+00:00
-- url     : https://prove2.me/theorems/2b4cf4a5-3677-49d1-aca0-6e54a179bb4f
-- title:
--   Ternary Entropy Rates: actual output rate
-- statement:
--   The Ternary Entropy Rates construction uses the actual output rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L111-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L111-L113

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.TernaryEntropyRates.actual_output_rate : Tendsto outputRate atTop (𝓝 TernaryParameters.Hpi) := by sorry
