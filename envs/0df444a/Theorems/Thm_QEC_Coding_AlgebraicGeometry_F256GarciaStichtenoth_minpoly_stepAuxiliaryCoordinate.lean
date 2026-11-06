-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_minpoly_stepAuxiliaryCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.minpoly_stepAuxiliaryCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:29.393267+00:00
-- url     : https://prove2.me/theorems/4f17476a-a936-4862-94b2-1e764336e46e
-- title:
--   F256 Garcia Stichtenoth: minpoly step Auxiliary Coordinate
-- statement:
--   The minimal polynomial of the actual auxiliary coordinate is the literal
--   Artin--Schreier polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L121-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L121-L140

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.minpoly_stepAuxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly K (stepAuxiliaryCoordinate P x hx) =
      stepAuxiliaryPolynomial x := by sorry
