-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_values_increasing
-- name    : ThreeSum.LightPrimePool.values_increasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:28.323715+00:00
-- url     : https://prove2.me/theorems/af4b4e80-e79a-4897-a236-75da12070070
-- title:
--   Light Prime Pool: values increasing
-- statement:
--   The Light Prime Pool construction uses the values increasing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L81-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L81-L81

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimePool.values_increasing (y : ℕ) : (values y).Pairwise (· < ·) := by sorry
