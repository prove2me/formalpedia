-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differential_eq_functionFieldDerivation_smul_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:10.352616+00:00
-- url     : https://prove2.me/theorems/6e3789d5-e611-47f3-b0c9-0e56b3de08cd
-- title:
--   Function Field Differential: differential eq function Field Derivation smul generator
-- statement:
--   The universal differential of a function is its function-field derivative
--   times the chosen global differential generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L198-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L198-L208

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differential_eq_functionFieldDerivation_smul_generator (f : F) :
    differential k F f = functionFieldDerivation (k := k) (F := F) f •
      functionFieldDifferentialGenerator (k := k) (F := F) := by sorry
