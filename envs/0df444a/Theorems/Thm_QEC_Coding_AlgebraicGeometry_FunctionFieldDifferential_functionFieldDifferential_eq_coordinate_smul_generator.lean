-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferential_eq_coordinate_smul_generator
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferential_eq_coordinate_smul_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:52.323611+00:00
-- url     : https://prove2.me/theorems/4d135cc2-c179-4039-a426-1839dcc5bf7a
-- title:
--   Function Field Differential: function Field Differential eq coordinate smul generator
-- statement:
--   Every function-field differential is its coordinate times the chosen
--   global differential generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L178-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L178-L185

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferential_eq_coordinate_smul_generator
    (omega : Differential k F) :
    omega = functionFieldDifferentialCoordinate (k := k) (F := F) omega •
      functionFieldDifferentialGenerator (k := k) (F := F) := by sorry
