-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_covers_raw_cap
-- name    : ThreeSum.TernaryCoverFrequency.covers_raw_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:23.129817+00:00
-- url     : https://prove2.me/theorems/24e8f7ce-d030-42c9-a483-a9c7f9b8e425
-- title:
--   Ternary Cover Frequency: covers raw cap
-- statement:
--   A positive retained hit certifies the full raw cap at every ordered
--   target pair, including pairs different from the one being covered.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L132-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L132-L140

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.TernaryCoverFrequency.covers_raw_cap {B τ : ℕ} {w : Weight m p} {t : ZMod p × ZMod p}
    (hc : Covers m p B τ w t) : rawCap (fixedAlpha m) (fixedPi m) w ≤ τ := by sorry
