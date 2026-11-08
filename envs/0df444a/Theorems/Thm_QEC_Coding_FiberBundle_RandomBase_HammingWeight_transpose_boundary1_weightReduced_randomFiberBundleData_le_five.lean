-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_le_five
-- name    : QEC.Coding.FiberBundle.RandomBase.HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:12.209339+00:00
-- url     : https://prove2.me/theorems/6b5ad895-4231-49dc-a7f7-a73eec90f5a6
-- title:
--   Random Base: Hamming Weight transpose boundary1 weight Reduced random Fiber Bundle Data le five
-- statement:
--   The HHO20 cycle fiber makes every X-check of the weight-reduced random
--   bundle have weight at most five.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L811-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L811-L827

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

theorem QEC.Coding.FiberBundle.RandomBase.HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_le_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (baseSupportRelation
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (i : ZMod (ell * ell)) :
    HammingWeight
        (wordLinearMapTranspose
          (boundary1 (weightReducedData
            (RandomTwist.fiberBundleData baseSample twistSample)))
          (Pi.single (q, i) 1)) ≤ 5 := by sorry
