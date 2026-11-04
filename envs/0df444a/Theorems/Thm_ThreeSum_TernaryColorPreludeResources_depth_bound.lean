-- Prove2me | Theorems.Thm_ThreeSum_TernaryColorPreludeResources_depth_bound
-- name    : ThreeSum.TernaryColorPreludeResources.depth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:02:02.068067+00:00
-- url     : https://prove2.me/theorems/6a687e0d-e621-4880-b1d4-9ac7a8926ded
-- title:
--   Ternary Color Prelude Resources: depth bound
-- statement:
--   The Ternary Color Prelude Resources construction uses the depth bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L52-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L52-L56

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.TernaryColorPreludeResources.depth_bound (n : ℕ) : depth n≤ 2*width n+n+18 := by sorry
