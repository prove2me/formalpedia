-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_boundary_columns_weightReduced_randomFiberBundleData_le_five
-- name    : QEC.Coding.FiberBundle.RandomBase.HammingWeight_boundary_columns_weightReduced_randomFiberBundleData_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:43:25.499285+00:00
-- url     : https://prove2.me/theorems/1988b539-062f-4e58-9897-aa24d17271bb
-- title:
--   Random Base: Hamming Weight boundary columns weight Reduced random Fiber Bundle Data le five
-- statement:
--   Every physical qubit of the weight-reduced HHO20 random bundle is incident
--   to at most five X- and Z-checks in total.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L887-L914
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L887-L914

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

theorem QEC.Coding.FiberBundle.RandomBase.HammingWeight_boundary_columns_weightReduced_randomFiberBundleData_le_five
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
    HammingWeight
        (boundary1 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (boundary2 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (reducedQubitBasisWord
            (RandomTwist.fiberBundleData baseSample twistSample) q)) ≤ 5 := by sorry
