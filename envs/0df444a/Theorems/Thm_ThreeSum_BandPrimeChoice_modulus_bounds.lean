-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
-- name    : ThreeSum.BandPrimeChoice.modulus_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:44.028338+00:00
-- url     : https://prove2.me/theorems/b9dbd63c-40da-4578-ad10-022cc48d9ffc
-- title:
--   Band Prime Choice: modulus bounds
-- statement:
--   The Band Prime Choice construction uses the modulus bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L66-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L66-L78

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC g A B C rs r ∧
      modulus primes s nA nB nC g A B C rs r ≤ Y^r := by sorry
