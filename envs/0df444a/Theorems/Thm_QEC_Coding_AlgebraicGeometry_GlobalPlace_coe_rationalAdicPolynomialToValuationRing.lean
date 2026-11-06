-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:26.751044+00:00
-- url     : https://prove2.me/theorems/4cc6e2be-ebf1-4967-b666-b7626bbc4cae
-- title:
--   Global Place: coe rational Adic Polynomial To Valuation Ring
-- statement:
--   The valuation-ring polynomial map has the expected ambient rational
--   function value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L99-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L99-L108

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicDecidableEq

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicPolynomialToValuationRing p b :
      (rationalAdic p).valuationRing) : RatFunc k) =
      algebraMap k[X] (RatFunc k) b := by sorry
