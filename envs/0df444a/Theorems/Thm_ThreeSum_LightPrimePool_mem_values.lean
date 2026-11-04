-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_mem_values
-- name    : ThreeSum.LightPrimePool.mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:59.914908+00:00
-- url     : https://prove2.me/theorems/5f629f4b-75b7-4a1e-ae41-b8570dde2397
-- title:
--   Light Prime Pool: mem values
-- statement:
--   The Light Prime Pool construction uses the mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L85-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L85-L92

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

theorem ThreeSum.LightPrimePool.mem_values {y p : ℕ} :
    p ∈ values y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4*y := by sorry
