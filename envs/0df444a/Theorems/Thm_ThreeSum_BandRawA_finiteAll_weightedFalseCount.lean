-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAll_weightedFalseCount
-- name    : ThreeSum.BandRawA.finiteAll_weightedFalseCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:14.329022+00:00
-- url     : https://prove2.me/theorems/3b78d147-cdf2-4277-8b5d-048c9cf41fc2
-- title:
--   Band Raw A: finite All weighted False Count
-- statement:
--   The Band Raw A construction uses the finite All weighted False Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L141-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L141-L152

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by sorry
