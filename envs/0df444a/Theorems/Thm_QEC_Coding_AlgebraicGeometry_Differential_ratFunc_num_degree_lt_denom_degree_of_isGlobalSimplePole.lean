-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:09.700668+00:00
-- url     : https://prove2.me/theorems/6b7a34e4-b440-48cf-a529-72de9e55dc18
-- title:
--   Differential: rat Func num degree lt denom degree of is Global Simple Pole
-- statement:
--   The normalized numerator of a globally simple-pole rational differential
--   has strictly smaller degree than its denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L75-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L75-L88

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    f.num.degree < f.denom.degree := by sorry
