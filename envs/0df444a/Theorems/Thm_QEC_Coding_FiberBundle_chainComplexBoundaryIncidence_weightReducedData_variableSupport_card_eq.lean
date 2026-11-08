-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq
-- name    : QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:54.848604+00:00
-- url     : https://prove2.me/theorems/895fc6db-46d3-4fb3-b226-b6c714030a9a
-- title:
--   Fiber Bundle: chain Complex Boundary Incidence weight Reduced Data variable Support card eq
-- statement:
--   The Fiber Bundle construction uses the chain Complex Boundary Incidence weight Reduced Data variable Support card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L658-L674
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L658-L674

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

theorem QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_card_eq
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card =
      HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) := by sorry
