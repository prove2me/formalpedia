-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_place_eq_rationalAdic
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_place_eq_rationalAdic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:29:09.575047+00:00
-- url     : https://prove2.me/theorems/f48c40b0-7137-428f-b568-bda0829b297a
-- title:
--   F256 Garcia Stichtenoth: base Rational Place place eq rational Adic
-- statement:
--   The place carried by `baseRationalPlace` is the adic place at its exposed
--   height-one centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L143-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L143-L146

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_place_eq_rationalAdic (a : BasePoint) :
    (baseRationalPlace a).place =
      GlobalPlace.rationalAdic (baseHeightOnePoint a) := by sorry
