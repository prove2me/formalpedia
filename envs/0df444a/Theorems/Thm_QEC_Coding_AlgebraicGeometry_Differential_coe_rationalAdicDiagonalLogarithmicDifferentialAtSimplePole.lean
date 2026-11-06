-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:02.181933+00:00
-- url     : https://prove2.me/theorems/7dc3b24a-f793-4bc3-875a-98eb7cb185ac
-- title:
--   Differential: coe rational Adic Diagonal Logarithmic Differential At Simple Pole
-- statement:
--   The ambient differential represented by the diagonal logarithmic trace
--   has the expected matrix-trace coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L92-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L92-L134

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k : Type*} [Field k]
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    ((rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix R *
              rationalDiagonalMatrixInverse a) *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (Matrix.diagonal a))) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
