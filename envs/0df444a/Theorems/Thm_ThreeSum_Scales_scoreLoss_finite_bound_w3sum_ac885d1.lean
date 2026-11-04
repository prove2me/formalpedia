-- Prove2me | Theorems.Thm_ThreeSum_Scales_scoreLoss_finite_bound_w3sum_ac885d1
-- name    : ThreeSum.Scales.scoreLoss_finite_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:46.053847+00:00
-- url     : https://prove2.me/theorems/d546e97d-0ec8-4ae1-9fe7-bd3465cb8ea8
-- title:
--   Scales: score Loss finite bound
-- statement:
--   A finite algebraic transfer of the actual prime-chain contraction to
--   the explicit accumulated score loss. The two count inequalities are the
--   outputs of `PrimeChain.modulus_score_bound` and `modulus_bounds`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L705-L735
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L705-L735

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.Scales.scoreLoss_finite_bound_w3sum_ac885d1 {k n H H₁ P : ℕ}
    (hC : 0 < (PrimeDensity.candidates (primeWindow n)).card)
    (hbudget : divisorBudget k n * primeWindow n ≤
      (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)))
    (hcontract : (PrimeDensity.candidates (primeWindow n)).card ^ primeDepth radix n * H ≤
      divisorBudget k n ^ primeDepth radix n * H₁)
    (hP : P ≤ (4 * primeWindow n) ^ primeDepth radix n) :
    P * H ≤ scoreLoss k n * H₁ := by sorry
