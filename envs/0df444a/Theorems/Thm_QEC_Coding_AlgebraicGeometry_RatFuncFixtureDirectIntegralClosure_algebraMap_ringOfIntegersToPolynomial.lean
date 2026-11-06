-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixtureDirectIntegralClosure_algebraMap_ringOfIntegersToPolynomial
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_ringOfIntegersToPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:27.679886+00:00
-- url     : https://prove2.me/theorems/c0fd301f-021b-483f-8919-7c1934da0cf3
-- title:
--   Rat Func Fixture Direct Integral Closure: algebra Map ring Of Integers To Polynomial
-- statement:
--   The Rat Func Fixture Direct Integral Closure construction uses the algebra Map ring Of Integers To Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalIntegralClosure.lean#L27-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalIntegralClosure.lean#L27-L29

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

theorem QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure.algebraMap_ringOfIntegersToPolynomial (b : B) :
    algebraMap K[X] F (ringOfIntegersToPolynomial b) = algebraMap B F b := by sorry
