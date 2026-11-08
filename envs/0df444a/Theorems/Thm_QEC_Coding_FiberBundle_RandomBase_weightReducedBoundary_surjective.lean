-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weightReducedBoundary_surjective
-- name    : QEC.Coding.FiberBundle.RandomBase.weightReducedBoundary_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:21.901772+00:00
-- url     : https://prove2.me/theorems/9077e080-5242-40a0-8d63-3b0e2ed9a58d
-- title:
--   Random Base: weight Reduced Boundary surjective
-- statement:
--   Full row rank of the sampled Tanner matrix therefore implies
--   surjectivity of its internally weight-reduced boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L71-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L71-L88

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.weightReducedBoundary_surjective
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Function.Surjective
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample)) := by sorry
