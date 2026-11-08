-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_horizontal_basis_weight_le_one
-- name    : QEC.Coding.FiberBundle.weightReductionForwardMap1_horizontal_basis_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:36.675386+00:00
-- url     : https://prove2.me/theorems/aa16c26b-6b82-49c2-a6b7-14620d647b2b
-- title:
--   Fiber Bundle: weight Reduction Forward Map1 horizontal basis weight le one
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Forward Map1 horizontal basis weight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L154-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L154-L195

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.weightReductionForwardMap1_horizontal_basis_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inl (q, i)))) ≤ 1 := by sorry
