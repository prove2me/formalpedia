-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_aeval
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:20.358198+00:00
-- url     : https://prove2.me/theorems/46fc2981-929d-40df-8329-58fee622bc81
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Polynomial aeval
-- statement:
--   The actual auxiliary coordinate is a root of its literal source
--   polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L61-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AuxiliaryMinpoly.lean#L61-L72

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_aeval
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (stepAuxiliaryCoordinate P x hx)
        (stepAuxiliaryPolynomial x) = 0 := by sorry
