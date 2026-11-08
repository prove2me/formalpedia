-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_single_apply
-- name    : QEC.Coding.FiberBundle.wordLinearMapTranspose_single_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:21:47.427635+00:00
-- url     : https://prove2.me/theorems/d4a21524-f820-4ccc-9b2a-e025eed3fa51
-- title:
--   Fiber Bundle: word Linear Map Transpose single apply
-- statement:
--   The Fiber Bundle construction uses the word Linear Map Transpose single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L239-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L239-L252

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

theorem QEC.Coding.FiberBundle.wordLinearMapTranspose_single_apply
    {F I K : Type*} [Field F] [Fintype F]
    [Fintype I] [Fintype K]
    (A : Word F I →ₗ[F] Word F K) (k : K) (q : I) :
    wordLinearMapTranspose A (canonicalBasisWord (F := F) k) q =
      A (canonicalBasisWord (F := F) q) k := by sorry
