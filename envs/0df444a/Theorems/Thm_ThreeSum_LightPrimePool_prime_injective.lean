-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_injective
-- name    : ThreeSum.LightPrimePool.prime_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:19.800352+00:00
-- url     : https://prove2.me/theorems/5c55fb22-7b28-4953-b7cd-8c6e2d5f303a
-- title:
--   Light Prime Pool: prime injective
-- statement:
--   The Light Prime Pool construction uses the prime injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L111-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L111-L113

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

theorem ThreeSum.LightPrimePool.prime_injective {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j := by sorry
