-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:03:29.341033+00:00
-- url     : https://prove2.me/theorems/ab1c391a-ff51-452c-9e78-7246f55051c0
-- title:
--   F256 Garcia Stichtenoth: split Upper Rational Place evaluate step Distinguished Coordinate ne zero
-- statement:
--   The successor distinguished coordinate has nonzero residue at every
--   split upper rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitEvaluation.lean#L175-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitEvaluation.lean#L175-L226

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hvalue : Q.evaluateRegular x hregular ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperRationalPlace Q P x hx hregular c).evaluateRegular
        (stepDistinguishedCoordinate P x hx)
        (splitAbovePlace_stepDistinguishedCoordinate_regular
          Q P x hx hregular hvalue c) ≠ 0 := by sorry
