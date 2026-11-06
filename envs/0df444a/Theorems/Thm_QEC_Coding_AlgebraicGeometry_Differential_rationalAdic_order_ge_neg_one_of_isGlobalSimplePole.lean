-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:12.85531+00:00
-- url     : https://prove2.me/theorems/6a32481c-3706-452f-bad6-a6054026a99c
-- title:
--   Differential: rational Adic order ge neg one of is Global Simple Pole
-- statement:
--   A globally simple-pole differential `f dX` forces `f` to have order at
--   least `-1` at every finite normalized rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L36-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L36-L52

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k)))
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    -1 ≤ (GlobalPlace.rationalAdic p).order f := by sorry
