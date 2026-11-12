-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:57:04.508365+00:00
-- url     : https://prove2.me/theorems/e3942ffb-9bea-4a23-801f-a34f89d40c17
-- title:
--   Cartwright Steger: base Norm One Order Units Reduction surjective iff PSL le image
-- statement:
--   The intrinsic base-field norm-one order units have surjective finite
--   reduction exactly when the explicit finite Cartwright--Steger image contains
--   the full selected `PSL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L160-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L160-L165

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by sorry
