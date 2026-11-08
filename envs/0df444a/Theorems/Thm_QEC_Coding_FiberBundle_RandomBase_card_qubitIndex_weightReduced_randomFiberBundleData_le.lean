-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_qubitIndex_weightReduced_randomFiberBundleData_le
-- name    : QEC.Coding.FiberBundle.RandomBase.card_qubitIndex_weightReduced_randomFiberBundleData_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:43:29.108399+00:00
-- url     : https://prove2.me/theorems/a54c8da4-5a77-4374-a32b-4d9da7014850
-- title:
--   Random Base: card qubit Index weight Reduced random Fiber Bundle Data le
-- statement:
--   Fully-good HHO20 samples incur only the explicit degree-window factor in
--   the physical-qubit count under weight reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L941-L973
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L941-L973

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

theorem QEC.Coding.FiberBundle.RandomBase.card_qubitIndex_weightReduced_randomFiberBundleData_le
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck
            (baseSupportRelation
              (RandomTwist.fiberBundleData baseSample twistSample)))
          (ClassicalWeightReduction.WeightReducedBit
            (baseSupportRelation
              (RandomTwist.fiberBundleData baseSample twistSample)))
          (ZMod (ell * ell)) (ZMod (ell * ell))) ≤
      1616 * r * Delta * (ell * ell) := by sorry
