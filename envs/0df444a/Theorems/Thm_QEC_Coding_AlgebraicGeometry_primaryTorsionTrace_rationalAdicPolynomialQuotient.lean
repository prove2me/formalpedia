-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_rationalAdicPolynomialQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:56.674269+00:00
-- url     : https://prove2.me/theorems/14c5edb6-8451-4d1f-a778-c41a081cd8f5
-- title:
--   Algebraic Geometry: primary Torsion Trace rational Adic Polynomial Quotient
-- statement:
--   At a finite rational place, the primary trace on a polynomial cyclic
--   quotient is the principal-ideal multiplicity times the reduced multiplier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L103-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L103-L113

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r)
        (multiplicity p.asIdeal (Ideal.span {a})) =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by sorry
