-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialCoordinate_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:46.710213+00:00
-- url     : https://prove2.me/theorems/285a47b8-3146-4e12-b7e2-331061e0c8cc
-- title:
--   Function Field Differential: function Field Differential Coordinate differential
-- statement:
--   The differential coordinate evaluates a universal differential through the
--   constructed separable function-field derivation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L189-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L189-L194

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialCoordinate_differential (f : F) :
    functionFieldDifferentialCoordinate (k := k) (F := F) (differential k F f) =
      functionFieldDerivation (k := k) (F := F) f := by sorry
