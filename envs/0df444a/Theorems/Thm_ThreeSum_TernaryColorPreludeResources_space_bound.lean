-- Prove2me | Theorems.Thm_ThreeSum_TernaryColorPreludeResources_space_bound
-- name    : ThreeSum.TernaryColorPreludeResources.space_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:00:43.246856+00:00
-- url     : https://prove2.me/theorems/28824075-4903-4bd9-989f-bb3e45108700
-- title:
--   Ternary Color Prelude Resources: space bound
-- statement:
--   The Ternary Color Prelude Resources construction uses the space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L40-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L40-L43

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_WeightedCache3SUM_Alias_5ff3e9fe041ca03d

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.TernaryColorPreludeResources.space_bound (free n : ℕ) : space free n≤ free+14*n+width n+16 := by sorry
