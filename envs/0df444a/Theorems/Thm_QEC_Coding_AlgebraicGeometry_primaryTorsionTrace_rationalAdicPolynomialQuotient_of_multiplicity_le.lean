-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_rationalAdicPolynomialQuotient_of_multiplicity_le
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient_of_multiplicity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:08.114075+00:00
-- url     : https://prove2.me/theorems/0216c735-f159-4632-8281-3cd5ed21b200
-- title:
--   Algebraic Geometry: primary Torsion Trace rational Adic Polynomial Quotient of multiplicity le
-- statement:
--   At a finite rational place, the stabilized primary trace on a polynomial
--   cyclic quotient is the principal-ideal multiplicity times the reduced
--   multiplier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L171-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L171-L181

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_rationalAdicPolynomialQuotient_of_multiplicity_le
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (a : k[X]) (ha : a ≠ 0) (r : k[X]) (n : ℕ)
    (hpn : multiplicity p.asIdeal (Ideal.span {a}) ≤ n) :
    primaryTorsionTrace p.asIdeal (cyclicQuotientMul a r) n =
      (multiplicity p.asIdeal (Ideal.span {a}) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal r := by sorry
