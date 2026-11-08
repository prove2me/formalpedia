-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:38.562877+00:00
-- url     : https://prove2.me/theorems/d928143d-cff9-45ac-8fa6-3ac2ab53de54
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary2 reduced Qubit Basis Word inl eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight transpose boundary2 reduced Qubit Basis Word inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L528-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L528-L540

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
    (b : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inl (b, i)))) =
      HammingWeight (fun j => D.fiberBoundary i j) := by sorry
