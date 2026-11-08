-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_boundary1_reducedQubitBasisWord
-- name    : QEC.Coding.FiberBundle.boundary1_reducedQubitBasisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:24.673393+00:00
-- url     : https://prove2.me/theorems/394fec4c-76b0-41f0-a7e1-4a5509e223a7
-- title:
--   Fiber Bundle: boundary1 reduced Qubit Basis Word
-- statement:
--   The Fiber Bundle construction uses the boundary1 reduced Qubit Basis Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L450-L471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L450-L471

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

theorem QEC.Coding.FiberBundle.boundary1_reducedQubitBasisWord
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    boundary1 (weightReducedData D) (reducedQubitBasisWord D q) =
      fun p => boundary1Matrix (weightReducedData D) p q := by sorry
