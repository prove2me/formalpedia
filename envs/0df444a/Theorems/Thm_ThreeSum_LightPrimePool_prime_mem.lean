-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_mem
-- name    : ThreeSum.LightPrimePool.prime_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:43.63138+00:00
-- url     : https://prove2.me/theorems/0e6d5890-a3dc-4c77-a668-9b5422e3968d
-- title:
--   Light Prime Pool: prime mem
-- statement:
--   The Light Prime Pool construction uses the prime mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L102-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L102-L105

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

theorem ThreeSum.LightPrimePool.prime_mem {y i : ℕ} (hi : i < size y) : prime y i ∈ values y := by sorry
