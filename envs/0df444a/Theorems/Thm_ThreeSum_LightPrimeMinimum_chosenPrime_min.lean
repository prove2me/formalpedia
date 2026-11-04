-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenPrime_min
-- name    : ThreeSum.LightPrimeMinimum.chosenPrime_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:37.604524+00:00
-- url     : https://prove2.me/theorems/492893ab-6c62-4d39-8261-744c4223ebac
-- title:
--   Light Prime Minimum: chosen Prime min
-- statement:
--   The Light Prime Minimum construction uses the chosen Prime min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L34-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L34-L41

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeMinimum.chosenPrime_min (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) {i : ℕ} (hi : i < s) :
    score primes s (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C ≤
      score primes s (q*primes i) nA nB nC A B C := by sorry
