-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_chosenIndex_lt
-- name    : ThreeSum.BandPrimeChoice.chosenIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:12.284217+00:00
-- url     : https://prove2.me/theorems/ab18cbb5-2543-43e4-bce1-a9b650587d9a
-- title:
--   Band Prime Choice: chosen Index lt
-- statement:
--   The Band Prime Choice construction uses the chosen Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L31-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L31-L33

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenIndex_lt

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := by sorry
