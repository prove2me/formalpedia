-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:40.578468+00:00
-- url     : https://prove2.me/theorems/7716e882-2b7c-47c6-a6db-806945b67cd2
-- title:
--   Global Place: rational Adic Polynomial irreducible
-- statement:
--   The chosen polynomial representative is irreducible.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L53-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean#L53-L59

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    Irreducible (rationalAdicPolynomial p) := by sorry
