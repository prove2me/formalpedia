-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_horizontal_auxiliary_expansion
-- name    : QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_horizontal_auxiliary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:17:29.757269+00:00
-- url     : https://prove2.me/theorems/957cb276-7a7d-4065-8fd0-aa259014f427
-- title:
--   Fiber Bundle: weight Reduction Inverse Map1 transpose horizontal auxiliary expansion
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Inverse Map1 transpose horizontal auxiliary expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L362-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L362-L443

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

theorem QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_horizontal_auxiliary_expansion
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (k : fiberZero) :
    wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D (Sum.inl (Sum.inr a, k))) =
      ∑ nb : ClassicalWeightReduction.CheckNeighbor R a.1,
        inverseAuxiliaryCoefficient D nb.1 a •
          Pi.single
            (Sum.inl
              (nb.1, (D.connection nb.1 a.1).onZero.symm k)) 1 := by sorry
