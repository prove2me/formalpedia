-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
-- name    : QEC.Coding.AlgebraicGeometry.simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:34:05.468144+00:00
-- url     : https://prove2.me/theorems/151127fa-ba4a-44a6-ae5f-5c88465a780e
-- title:
--   Algebraic Geometry: simple Pole Residue polynomial Matrix Logarithmic Trace Differential
-- statement:
--   Polynomial matrix logarithmic trace terms have zero normalized residue at
--   every finite rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialMatrixResidue.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialMatrixResidue.lean#L75-L83

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P) = 0 := by sorry
