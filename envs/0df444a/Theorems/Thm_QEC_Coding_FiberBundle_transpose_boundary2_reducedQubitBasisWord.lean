-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_transpose_boundary2_reducedQubitBasisWord
-- name    : QEC.Coding.FiberBundle.transpose_boundary2_reducedQubitBasisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:26.817773+00:00
-- url     : https://prove2.me/theorems/64001e97-107f-4aeb-af92-4501091a97df
-- title:
--   Fiber Bundle: transpose boundary2 reduced Qubit Basis Word
-- statement:
--   The Fiber Bundle construction uses the transpose boundary2 reduced Qubit Basis Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L473-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L473-L494

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

theorem QEC.Coding.FiberBundle.transpose_boundary2_reducedQubitBasisWord
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    wordLinearMapTranspose (boundary2 (weightReducedData D))
        (reducedQubitBasisWord D q) =
      fun p => boundary2Matrix (weightReducedData D) q p := by sorry
