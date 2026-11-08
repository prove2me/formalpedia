-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
-- name    : QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:16:25.830737+00:00
-- url     : https://prove2.me/theorems/c664f6f0-90a0-48e9-b59c-f64229174d1f
-- title:
--   Fiber Bundle: weight Reduction Inverse Map1 transpose horizontal primary weight le one
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Inverse Map1 transpose horizontal primary weight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L445-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L445-L466

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

theorem QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (k : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inl (Sum.inl e, k)))) ≤ 1 := by sorry
