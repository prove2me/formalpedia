-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_zero_spec
-- name    : ThreeSum.LightPrimePool.prime_zero_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:30.038903+00:00
-- url     : https://prove2.me/theorems/b592305a-74cb-4c99-9b22-c4b5983f17a8
-- title:
--   Light Prime Pool: prime zero spec
-- statement:
--   The Light Prime Pool construction uses the prime zero spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L140-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L140-L145

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

theorem ThreeSum.LightPrimePool.prime_zero_spec {y : ℕ} (hy : 0 < y) :
    Nat.Prime (prime y 0) ∧ y < prime y 0 ∧ prime y 0 ≤ 2*y := by sorry
