-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_chosenPrime_min
-- name    : ThreeSum.BandPrimeChoice.chosenPrime_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:42.348803+00:00
-- url     : https://prove2.me/theorems/b6d44c89-34bc-42f5-b4dd-54860cd753d4
-- title:
--   Band Prime Choice: chosen Prime min
-- statement:
--   The Band Prime Choice construction uses the chosen Prime min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L35-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L35-L41

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenPrime_min

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.chosenPrime_min (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {i : ℕ} (hi : i < s) :
    score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      score primes s (q*primes i) nA nB nC g A B C rs := by sorry
