-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_rationalAdicSimpleFraction
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalAdicSimpleFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:35.722087+00:00
-- url     : https://prove2.me/theorems/7c60fa7f-7f44-4de8-8d2b-6a68d740c67a
-- title:
--   Differential: simple Pole Trace Residue rational Adic Simple Fraction
-- statement:
--   The traced normalized residue of the finite rational simple fraction
--   `(b / q) dX` is the next-to-leading coefficient of `b`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSimpleFractionResidue.lean#L247-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSimpleFractionResidue.lean#L247-L290

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalAdicSimpleFraction
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial p).degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b :
          Differential k (RatFunc k))
        (rationalAdicSimpleFractionAtSimplePole p b).property =
      b.coeff ((GlobalPlace.rationalAdicPolynomial p).natDegree - 1) := by sorry
