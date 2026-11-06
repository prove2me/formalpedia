-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_uniformizerLogDifferentialClass_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.uniformizerLogDifferentialClass_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:53.473561+00:00
-- url     : https://prove2.me/theorems/c7cad6e0-68ad-46e9-adc3-c5190beea96a
-- title:
--   Differential: uniformizer Log Differential Class ne zero
-- statement:
--   The normalized uniformizer's logarithmic differential represents a
--   nonzero class in the simple-pole quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L294-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L294-L343

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.uniformizerLogDifferentialClass_ne_zero (P : GlobalPlace k F) :
    uniformizerLogDifferentialClass (k := k) (F := F) P ≠ 0 := by sorry
