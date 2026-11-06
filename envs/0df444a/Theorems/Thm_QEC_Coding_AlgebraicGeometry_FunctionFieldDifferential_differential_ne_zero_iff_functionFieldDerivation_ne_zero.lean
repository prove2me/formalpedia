-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_ne_zero_iff_functionFieldDerivation_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differential_ne_zero_iff_functionFieldDerivation_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:19.351644+00:00
-- url     : https://prove2.me/theorems/f53a7f4b-dd4d-4d84-9f9d-7b5ebae9661b
-- title:
--   Function Field Differential: differential ne zero iff function Field Derivation ne zero
-- statement:
--   A universal differential vanishes exactly when its function-field
--   derivative vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L212-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L212-L225

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differential_ne_zero_iff_functionFieldDerivation_ne_zero (f : F) :
    differential k F f ≠ 0 ↔ functionFieldDerivation (k := k) (F := F) f ≠ 0 := by sorry
