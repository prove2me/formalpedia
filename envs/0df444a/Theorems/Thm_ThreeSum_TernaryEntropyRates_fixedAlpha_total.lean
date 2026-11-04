-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_fixedAlpha_total
-- name    : ThreeSum.TernaryEntropyRates.fixedAlpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:41.285508+00:00
-- url     : https://prove2.me/theorems/d84c1ea9-cea3-4c62-8b32-02920979efcb
-- title:
--   Ternary Entropy Rates: fixed Alpha total
-- statement:
--   The Ternary Entropy Rates construction uses the fixed Alpha total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L85-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L85-L87

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

theorem ThreeSum.TernaryEntropyRates.fixedAlpha_total (m : ℕ) : fixedAlpha m 0+fixedAlpha m 1+fixedAlpha m 2=fixedLength m := by sorry
