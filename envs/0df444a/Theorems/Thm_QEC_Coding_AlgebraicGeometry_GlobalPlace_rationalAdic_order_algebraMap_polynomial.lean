-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdic_order_algebraMap_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_order_algebraMap_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:23.01876+00:00
-- url     : https://prove2.me/theorems/9d66dbcd-e22a-4add-81b0-4f69e7779c98
-- title:
--   Global Place: rational Adic order algebra Map polynomial
-- statement:
--   The order of a nonzero polynomial at a finite rational place is the
--   multiplicity of the corresponding principal ideal at the height-one prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L33-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L33-L40

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_order_algebraMap_polynomial
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (a : k[X]) (ha : a ≠ 0) :
    (rationalAdic p).order (algebraMap k[X] (RatFunc k) a) =
      (multiplicity p.asIdeal (Ideal.span ({a} : Set k[X])) : ℤ) := by sorry
