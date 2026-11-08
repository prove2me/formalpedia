-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weightReducedClassicalDistanceAtLeast
-- name    : QEC.Coding.FiberBundle.RandomBase.weightReducedClassicalDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:34.808024+00:00
-- url     : https://prove2.me/theorems/c9a3e4af-b576-49e2-b2d9-80cb23d88bcc
-- title:
--   Random Base: weight Reduced Classical Distance At Least
-- statement:
--   The matrix extracted from the weight-reduced boundary has the classical
--   distance required by the EKZ product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L229-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L229-L255

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.weightReducedClassicalDistanceAtLeast
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    DistanceBalancing.ClassicalDistanceAtLeast
      (LinearMap.toMatrix'
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample)))
      ((4 * r) / 5) := by sorry
