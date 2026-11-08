-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_reducedQubitBasisWord
-- name    : QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_reducedQubitBasisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:56.500077+00:00
-- url     : https://prove2.me/theorems/79ec7ec6-2119-40d4-82cb-c66adc694828
-- title:
--   Fiber Bundle: weight Reduction Inverse Map1 transpose reduced Qubit Basis Word
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Inverse Map1 transpose reduced Qubit Basis Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L342-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L342-L360

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

theorem QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_reducedQubitBasisWord
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D q) =
      fun source : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match source, q with
        | Sum.inl bi, Sum.inl target' =>
            weightReductionInverseBaseOneBasis D bi.1 bi.2 target'
        | Sum.inr aj, Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2 target'
        | _, _ => 0 := by sorry
