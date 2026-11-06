-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:58.471425+00:00
-- url     : https://prove2.me/theorems/c03c2571-7828-4513-b39d-60776cfd291c
-- title:
--   Function Field Differential: function Field Differential Generator ne zero
-- statement:
--   The chosen differential generator is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L167-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L167-L174

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero :
    functionFieldDifferentialGenerator (k := k) (F := F) ≠ 0 := by sorry
