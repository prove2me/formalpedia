-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_zero_le_mem
-- name    : ThreeSum.LightPrimePool.prime_zero_le_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:53.70706+00:00
-- url     : https://prove2.me/theorems/759a7c81-698d-4066-9388-bfc8a15eab57
-- title:
--   Light Prime Pool: prime zero le mem
-- statement:
--   The Light Prime Pool construction uses the prime zero le mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L135-L138

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

theorem ThreeSum.LightPrimePool.prime_zero_le_mem {y p : ℕ} (hp : p ∈ values y) : prime y 0 ≤ p := by sorry
