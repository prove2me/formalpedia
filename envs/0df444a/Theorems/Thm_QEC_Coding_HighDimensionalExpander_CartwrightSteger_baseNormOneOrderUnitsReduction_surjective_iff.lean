-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_surjective_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:14.24123+00:00
-- url     : https://prove2.me/theorems/f930975b-8144-4a90-95be-f438ff8bd085
-- title:
--   Cartwright Steger: base Norm One Order Units Reduction surjective iff
-- statement:
--   Finite surjectivity for intrinsic norm-one order units is exactly the
--   construction-owned split-coordinate strong-approximation endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L76-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L76-L87

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) ↔
      Function.Surjective (orderNormOneInnerFormReduction P r level) := by sorry
