-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos
-- name    : ThreeSum.TernaryEntropyRates.denominator_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:10.265478+00:00
-- url     : https://prove2.me/theorems/e821d73a-9d39-4405-aa0a-81b80b341f12
-- title:
--   Ternary Entropy Rates: denominator pos
-- statement:
--   The Ternary Entropy Rates construction uses the denominator pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L130-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L130-L133

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

theorem ThreeSum.TernaryEntropyRates.denominator_pos {m : ℕ} (hm : 0 < m) :
    0 < (fixedLength m : ℝ)*Real.log 2 := by sorry
