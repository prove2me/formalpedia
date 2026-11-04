-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeDepth_loss_bound_w3sum_ac885d1
-- name    : ThreeSum.Scales.primeDepth_loss_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:32.272197+00:00
-- url     : https://prove2.me/theorems/558ce042-1d47-4730-b15a-74def9cad146
-- title:
--   Scales: prime Depth loss bound
-- statement:
--   The greedy depth loses only `32*y*4^r` compared with the target radix.
--   This applies to the actual selected product as soon as its finite `y^r`
--   lower bound from `PrimeChain.modulus_bounds` is supplied.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L413-L432
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L413-L432

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

theorem ThreeSum.Scales.primeDepth_loss_bound_w3sum_ac885d1 (R : ℕ → ℕ) {n P : ℕ}
    (hP : primeWindow n ^ primeDepth R n ≤ P) :
    R n ≤ primeLoss R n * P := by sorry
