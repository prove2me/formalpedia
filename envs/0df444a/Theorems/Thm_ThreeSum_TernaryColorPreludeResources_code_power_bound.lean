-- Prove2me | Theorems.Thm_ThreeSum_TernaryColorPreludeResources_code_power_bound
-- name    : ThreeSum.TernaryColorPreludeResources.code_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:00:33.093249+00:00
-- url     : https://prove2.me/theorems/bc714d9e-690c-4560-bb23-6294f24b2b6a
-- title:
--   Ternary Color Prelude Resources: code power bound
-- statement:
--   The Ternary Color Prelude Resources construction uses the code power bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L29-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean#L29-L38

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

theorem ThreeSum.TernaryColorPreludeResources.code_power_bound (n : ℕ) : 2^(width n+1)≤ 4*(n+1) := by sorry
