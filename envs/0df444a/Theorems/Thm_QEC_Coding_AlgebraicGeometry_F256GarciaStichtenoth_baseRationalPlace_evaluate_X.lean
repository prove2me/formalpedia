-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_evaluate_X
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_evaluate_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:30.804225+00:00
-- url     : https://prove2.me/theorems/fefeb616-bd3c-46a6-b654-55ec299a633e
-- title:
--   F256 Garcia Stichtenoth: base Rational Place evaluate X
-- statement:
--   Residue evaluation at the selected base place sends `X` to its literal
--   nonzero coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L161-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L161-L210

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_evaluate_X (a : BasePoint) :
    (baseRationalPlace a).evaluateRegular RatFunc.X
        (baseRationalPlace_X_regular a) = (a : F256) := by sorry
