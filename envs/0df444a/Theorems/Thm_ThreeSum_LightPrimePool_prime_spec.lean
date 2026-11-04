-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
-- name    : ThreeSum.LightPrimePool.prime_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:25.530532+00:00
-- url     : https://prove2.me/theorems/c2b2dbe9-e710-4916-b3db-60468c51492d
-- title:
--   Light Prime Pool: prime spec
-- statement:
--   The Light Prime Pool construction uses the prime spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L107-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L107-L109

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

theorem ThreeSum.LightPrimePool.prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y := by sorry
