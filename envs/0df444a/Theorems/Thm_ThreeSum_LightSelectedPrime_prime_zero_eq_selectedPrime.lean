-- Prove2me | Theorems.Thm_ThreeSum_LightSelectedPrime_prime_zero_eq_selectedPrime
-- name    : ThreeSum.LightSelectedPrime.prime_zero_eq_selectedPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:34.783256+00:00
-- url     : https://prove2.me/theorems/67dc1681-33ac-4657-93eb-141e16a91ba2
-- title:
--   Light Selected Prime: prime zero eq selected Prime
-- statement:
--   The Light Selected Prime construction uses the prime zero eq selected Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L20-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L20-L29

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000

theorem ThreeSum.LightSelectedPrime.prime_zero_eq_selectedPrime (N : ℕ) :
    LightPrimePool.prime (rootCeiling N) 0 = selectedPrime N := by sorry
