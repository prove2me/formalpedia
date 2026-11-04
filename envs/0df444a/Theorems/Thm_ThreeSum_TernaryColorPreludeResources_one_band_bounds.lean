-- Prove2me | Theorems.Thm_ThreeSum_TernaryColorPreludeResources_one_band_bounds
-- name    : ThreeSum.TernaryColorPreludeResources.one_band_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:00:35.042204+00:00
-- url     : https://prove2.me/theorems/e33c1f07-7d1c-45e4-a9d7-5e3d8616d3a2
-- title:
--   Ternary Color Prelude Resources: one band bounds
-- statement:
--   The Ternary Color Prelude Resources construction uses the one band bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L14-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L14-L20

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

theorem ThreeSum.TernaryColorPreludeResources.one_band_bounds (n : ℕ) :
    BandPartition.size n n≤ 1 ∧ ColorBandBounds.count n n≤ 3 ∧ ColorBandBounds.width n n≤ 2 := by sorry
