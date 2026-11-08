-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_vertical_primary_weight_le_one
-- name    : QEC.Coding.FiberBundle.weightReductionForwardMap1_vertical_primary_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:45.558977+00:00
-- url     : https://prove2.me/theorems/db6d50c9-c8de-4c65-ba15-1d340bc1d77c
-- title:
--   Fiber Bundle: weight Reduction Forward Map1 vertical primary weight le one
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Forward Map1 vertical primary weight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L197-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L197-L215

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

theorem QEC.Coding.FiberBundle.weightReductionForwardMap1_vertical_primary_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j)))) ≤ 1 := by sorry
