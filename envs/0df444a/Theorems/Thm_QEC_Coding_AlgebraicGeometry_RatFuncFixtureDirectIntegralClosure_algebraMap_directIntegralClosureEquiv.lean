-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixtureDirectIntegralClosure_algebraMap_directIntegralClosureEquiv
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_directIntegralClosureEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:25.540772+00:00
-- url     : https://prove2.me/theorems/429ec203-b0df-4d81-bb7f-86369a306b82
-- title:
--   Rat Func Fixture Direct Integral Closure: algebra Map direct Integral Closure Equiv
-- statement:
--   The Rat Func Fixture Direct Integral Closure construction uses the algebra Map direct Integral Closure Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalIntegralClosure.lean#L31-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalIntegralClosure.lean#L31-L34

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_13
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure._p2m_local_instance_c6523eaeb4_18

theorem QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_directIntegralClosureEquiv (p : K[X]) :
    algebraMap B F (directIntegralClosureEquiv p) = algebraMap K[X] F p := by sorry
