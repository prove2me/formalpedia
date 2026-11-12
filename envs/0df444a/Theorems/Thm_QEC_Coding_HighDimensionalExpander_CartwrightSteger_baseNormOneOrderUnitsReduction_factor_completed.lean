-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_factor_completed
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_factor_completed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:34.426554+00:00
-- url     : https://prove2.me/theorems/833daa35-3b4b-4a53-8fb3-8580c7f43e27
-- title:
--   Cartwright Steger: base Norm One Order Units Reduction factor completed
-- statement:
--   The Cartwright Steger construction uses the base Norm One Order Units Reduction factor completed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L41-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L41-L49

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_factor_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerBaseNormOneOrderUnits P r) :
    baseNormOneOrderUnitsReduction P r level u =
      specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level
          (baseNormOneOrderUnitsToCompleted P r level u)) := by sorry
