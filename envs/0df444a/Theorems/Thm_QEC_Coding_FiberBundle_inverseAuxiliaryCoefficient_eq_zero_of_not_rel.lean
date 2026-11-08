-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_inverseAuxiliaryCoefficient_eq_zero_of_not_rel
-- name    : QEC.Coding.FiberBundle.inverseAuxiliaryCoefficient_eq_zero_of_not_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:16:24.706708+00:00
-- url     : https://prove2.me/theorems/25088d60-2ec0-49bb-aa45-e833a8c73e1e
-- title:
--   Fiber Bundle: inverse Auxiliary Coefficient eq zero of not rel
-- statement:
--   The Fiber Bundle construction uses the inverse Auxiliary Coefficient eq zero of not rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L316-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L316-L340

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

theorem QEC.Coding.FiberBundle.inverseAuxiliaryCoefficient_eq_zero_of_not_rel
    (b : baseOne) (a : ClassicalWeightReduction.AuxiliaryBit R)
    (hba : ¬R a.1 b) :
    inverseAuxiliaryCoefficient D b a = 0 := by sorry
