-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:48.966922+00:00
-- url     : https://prove2.me/theorems/c99a5bfc-2298-4a01-b4a7-16baaa2c0780
-- title:
--   Cartwright Steger: order Norm One Inner Form Reduction surjective iff PSL le ambient
-- statement:
--   The full-inner-form formulation is literally the explicit finite ambient
--   formulation, by the proved lattice-times-stabilizer decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L122-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L122-L127

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerAmbient P r level := by sorry
