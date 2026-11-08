-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:48.934653+00:00
-- url     : https://prove2.me/theorems/7224c4a8-6f38-4311-9c7d-7bd5eed03ea2
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary2 reduced Qubit Basis Word inr eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight transpose boundary2 reduced Qubit Basis Word inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L542-L557
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L542-L557

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
    (a : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D (Sum.inr (a, j)))) =
      HammingWeight
        (fun b => (weightReducedData D).baseBoundary a b) := by sorry
