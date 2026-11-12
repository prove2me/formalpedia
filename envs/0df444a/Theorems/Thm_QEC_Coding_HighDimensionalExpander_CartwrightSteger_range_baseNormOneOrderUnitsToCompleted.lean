-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_baseNormOneOrderUnitsToCompleted
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_baseNormOneOrderUnitsToCompleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:38.941569+00:00
-- url     : https://prove2.me/theorems/96ccbff5-421a-41af-b229-b6722a30dc83
-- title:
--   Cartwright Steger: range base Norm One Order Units To Completed
-- statement:
--   Passing from split coordinates to all actual norm-one order units does
--   not change the completed image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L53-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L53-L64

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_baseNormOneOrderUnitsToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set.range (baseNormOneOrderUnitsToCompleted P r level) =
      Set.range (orderNormOneInnerFormToCompleted P r level) := by sorry
