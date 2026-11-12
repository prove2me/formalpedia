-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_baseNormOneOrderUnitsToCompleted_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_baseNormOneOrderUnitsToCompleted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:13:54.241796+00:00
-- url     : https://prove2.me/theorems/f2e4c3d4-8d34-4465-8dd8-eb511aff9dd3
-- title:
--   Cartwright Steger: dense Range base Norm One Order Units To Completed iff
-- statement:
--   The Cartwright Steger construction uses the dense Range base Norm One Order Units To Completed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L66-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L66-L72

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_baseNormOneOrderUnitsToCompleted_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (baseNormOneOrderUnitsToCompleted P r level) ↔
      DenseRange (orderNormOneInnerFormToCompleted P r level) := by sorry
