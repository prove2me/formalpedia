-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:14.285357+00:00
-- url     : https://prove2.me/theorems/98d13a4c-ab64-45a4-93be-b748972eb0d8
-- title:
--   Cartwright Steger: order Norm One Inner Form Reduction surjective iff PSL le inner Form Image
-- statement:
--   Surjectivity of the genuine norm-one reduction is equivalent to placing
--   the full finite `PSL` inside the reduction image of all actual inner-form
--   integral points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L101-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L101-L118

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexInnerFormImage P r level := by sorry
