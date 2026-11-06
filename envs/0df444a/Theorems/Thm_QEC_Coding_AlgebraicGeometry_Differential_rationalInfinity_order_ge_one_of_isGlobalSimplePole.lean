-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalInfinity_order_ge_one_of_isGlobalSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.rationalInfinity_order_ge_one_of_isGlobalSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:15.301889+00:00
-- url     : https://prove2.me/theorems/cb150a91-7dd8-46b2-bd5b-812f3bd8b2fe
-- title:
--   Differential: rational Infinity order ge one of is Global Simple Pole
-- statement:
--   A globally simple-pole differential `f dX` forces `f` to vanish to order
--   at least one at the normalized rational place at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L56-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimplePoleDenominator.lean#L56-L71

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.rationalInfinity_order_ge_one_of_isGlobalSimplePole
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    1 ≤ (GlobalPlace.rationalInfinity k).order f := by sorry
