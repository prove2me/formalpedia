-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:07.786707+00:00
-- url     : https://prove2.me/theorems/24790a69-da11-470b-93e7-108faf0776d2
-- title:
--   Differential: simple Pole Residue rational Adic Diagonal Logarithmic Differential
-- statement:
--   The normalized residue of the diagonal matrix logarithmic differential
--   is the finite sum of reduced diagonal coefficients weighted by the exact
--   principal-ideal multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L139-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicDiagonalMatrixResidue.lean#L139-L156

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha) =
      ∑ i, (GlobalPlace.rationalAdic p).residue
          (GlobalPlace.rationalAdicPolynomialToValuationRing p (R i i)) *
        (multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) :
          (GlobalPlace.rationalAdic p).residueField) := by sorry
