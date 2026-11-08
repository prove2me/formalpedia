-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero
-- name    : QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:17:36.668949+00:00
-- url     : https://prove2.me/theorems/2e5fe524-15b5-439b-ae3f-b59a55c194c7
-- title:
--   Fiber Bundle: weight Reduction Inverse Map1 transpose vertical auxiliary weight eq zero
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Inverse Map1 transpose vertical auxiliary weight eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L542-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L542-L559

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

theorem QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryCheck R) (k : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D (Sum.inr (Sum.inr a, k)))) = 0 := by sorry
