-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenIndex_lt
-- name    : ThreeSum.LightPrimeMinimum.chosenIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:57.635801+00:00
-- url     : https://prove2.me/theorems/6d50ff25-1a27-4ba3-96e5-e9cdd7967f08
-- title:
--   Light Prime Minimum: chosen Index lt
-- statement:
--   The Light Prime Minimum construction uses the chosen Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeMinimum.chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC : ℕ}
    (A B C : ℕ → ℤ) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC A B C < s := by sorry
