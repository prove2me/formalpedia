-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
-- name    : QEC.Coding.FiberBundle.RandomBase.chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:43:37.937545+00:00
-- url     : https://prove2.me/theorems/122d69d6-36d5-4262-aa03-c80d061e7413
-- title:
--   Random Base: chain Complex Boundary Incidence weight Reduced random Fiber Bundle Data variable Support le five
-- statement:
--   The actual HHO20 chain-complex incidence has variable degree at most five,
--   not merely a matrix-column proxy for that degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L918-L937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L918-L937

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ClassicalWeightReduction.WeightReducedBit
        (baseSupportRelation
          (RandomTwist.fiberBundleData baseSample twistSample)))
      (ZMod (ell * ell)) (ZMod (ell * ell))) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample)))).variableSupport q).card ≤ 5 := by sorry
