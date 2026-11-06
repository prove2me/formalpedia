-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:59.252247+00:00
-- url     : https://prove2.me/theorems/7f1aacbb-1e2c-43ba-bf6c-a61d24082762
-- title:
--   Global Place: rational Adic Ideal Residue Equiv mk
-- statement:
--   The rational-place ideal-quotient equivalence sends a polynomial class
--   to the actual reduction of that polynomial in the valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L44-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L44-L51

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    rationalAdicIdealResidueEquiv p (Ideal.Quotient.mk p.asIdeal b) =
      (rationalAdic p).residue
        (rationalAdicPolynomialToValuationRing p b) := by sorry
