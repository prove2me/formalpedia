-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:49.517855+00:00
-- url     : https://prove2.me/theorems/3746fd63-40a5-491c-9542-d39f02813d66
-- title:
--   Global Place: rational Adic Polynomial monic
-- statement:
--   The chosen polynomial representative is monic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L46-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L46-L50

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_monic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (rationalAdicPolynomial p).Monic := by sorry
