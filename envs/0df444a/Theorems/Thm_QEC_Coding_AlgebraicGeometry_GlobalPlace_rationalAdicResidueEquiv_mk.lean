-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:32.515111+00:00
-- url     : https://prove2.me/theorems/7c64443f-693f-473f-80f0-16a7e064d6ec
-- title:
--   Global Place: rational Adic Residue Equiv mk
-- statement:
--   The finite-place residue equivalence sends a polynomial class to the
--   actual reduction of that polynomial in the valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L128-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L128-L153

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    rationalAdicResidueEquiv p
        (AdjoinRoot.mk (rationalAdicPolynomial p) b) =
      (rationalAdic p).residue (rationalAdicPolynomialToValuationRing p b) := by sorry
