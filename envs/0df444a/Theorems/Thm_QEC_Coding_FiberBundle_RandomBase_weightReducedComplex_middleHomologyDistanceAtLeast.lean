-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weightReducedComplex_middleHomologyDistanceAtLeast
-- name    : QEC.Coding.FiberBundle.RandomBase.weightReducedComplex_middleHomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:13.146326+00:00
-- url     : https://prove2.me/theorems/d78aa54a-b507-431e-80f5-5f786afdf582
-- title:
--   Random Base: weight Reduced Complex middle Homology Distance At Least
-- statement:
--   Classical weight reduction preserves the random-base homological
--   distance because its forward middle map is one-Lipschitz.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L205-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L205-L225

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.weightReducedComplex_middleHomologyDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    MiddleHomologyDistanceAtLeast
      (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
        (incidenceRelation sample))
      ((4 * r) / 5) := by sorry
