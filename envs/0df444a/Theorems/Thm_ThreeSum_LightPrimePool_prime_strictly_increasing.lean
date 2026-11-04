-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_strictly_increasing
-- name    : ThreeSum.LightPrimePool.prime_strictly_increasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:26.107588+00:00
-- url     : https://prove2.me/theorems/84e3fa33-7733-4c73-8a93-d3a2117eba14
-- title:
--   Light Prime Pool: prime strictly increasing
-- statement:
--   The Light Prime Pool construction uses the prime strictly increasing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L115-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L115-L119

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

theorem ThreeSum.LightPrimePool.prime_strictly_increasing {y i j : ℕ}
    (hi : i < size y) (hj : j < size y) (hij : i < j) : prime y i < prime y j := by sorry
