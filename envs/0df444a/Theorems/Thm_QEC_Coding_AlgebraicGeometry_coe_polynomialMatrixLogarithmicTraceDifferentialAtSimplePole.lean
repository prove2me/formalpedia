-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:34:09.682213+00:00
-- url     : https://prove2.me/theorems/bf413df0-95ab-4ada-9420-262a05563aa5
-- title:
--   Algebraic Geometry: coe polynomial Matrix Logarithmic Trace Differential At Simple Pole
-- statement:
--   The ambient coefficient of the polynomial matrix logarithmic trace is
--   the expected fraction-field matrix trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialMatrixResidue.lean#L49-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialMatrixResidue.lean#L49-L71

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    ((polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P :
      Differential.simplePoleDifferentialLattice
        (GlobalPlace.rationalAdic p)) : Differential k (RatFunc k)) =
      Matrix.trace
          ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix P)) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
