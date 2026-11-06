-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_zeroBaseRationalPlace_order_X
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.zeroBaseRationalPlace_order_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:46:13.095641+00:00
-- url     : https://prove2.me/theorems/ddd694d1-1845-41d4-a946-5d158297a0cb
-- title:
--   F256 Garcia Stichtenoth: zero Base Rational Place order X
-- statement:
--   The base coordinate has a simple zero at the zero base place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ZeroPlace.lean#L160-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ZeroPlace.lean#L160-L167

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.zeroBaseRationalPlace_order_X :
    zeroBaseRationalPlace.place.order RatFunc.X = 1 := by sorry
