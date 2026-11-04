-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing_w3sum_ac885d1
-- name    : ThreeSum.LightPrimePool.prefix_increasing_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:27.676306+00:00
-- url     : https://prove2.me/theorems/3caadf82-8289-48f1-bc7c-a846e2209255
-- title:
--   Light Prime Pool: prefix increasing
-- statement:
--   The Light Prime Pool construction uses the prefix increasing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L60-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L60-L72

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

theorem ThreeSum.LightPrimePool.prefix_increasing_w3sum_ac885d1 (y i : ℕ) : (scanned y i).Pairwise (· < ·) := by sorry
