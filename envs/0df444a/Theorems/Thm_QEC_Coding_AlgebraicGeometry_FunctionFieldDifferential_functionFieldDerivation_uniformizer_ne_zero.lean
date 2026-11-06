-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_uniformizer_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_uniformizer_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:59.429716+00:00
-- url     : https://prove2.me/theorems/39d84250-c757-4b09-acca-f29362030224
-- title:
--   Function Field Differential: function Field Derivation uniformizer ne zero
-- statement:
--   The function-field derivative of the normalized valuation uniformizer is
--   nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L214-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L214-L229

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_uniformizer_ne_zero (P : GlobalPlace k F) :
    functionFieldDerivation (k := k) (F := F)
      (P.uniformizerInValuationRing : F) ≠ 0 := by sorry
