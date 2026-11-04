-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_physical_weighted_bound
-- name    : ThreeSum.BandRawA.physical_weighted_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:37.755935+00:00
-- url     : https://prove2.me/theorems/254600a3-5b55-4c2e-bf7e-30e1ec8475ed
-- title:
--   Band Raw A: physical weighted bound
-- statement:
--   The weighted score bound applies directly to the physical owner domain.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L105-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L105-L113

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.physical_weighted_bound (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < aux, Nat.Prime (primes i))
    (hinj : ∀ i < aux, ∀ j < aux, primes i=primes j → i=j) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q ≤ rs.length*(aux*g^3) := by sorry
