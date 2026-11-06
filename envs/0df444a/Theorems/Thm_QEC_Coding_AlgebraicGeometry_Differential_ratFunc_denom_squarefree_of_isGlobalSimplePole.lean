-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_ratFunc_denom_squarefree_of_isGlobalSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.ratFunc_denom_squarefree_of_isGlobalSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:12.697197+00:00
-- url     : https://prove2.me/theorems/b93157c7-489a-4206-8b4f-af59917397ca
-- title:
--   Differential: rat Func denom squarefree of is Global Simple Pole
-- statement:
--   The normalized denominator of a globally simple-pole rational
--   differential is squarefree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L92-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L92-L173

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.ratFunc_denom_squarefree_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    Squarefree f.denom := by sorry
