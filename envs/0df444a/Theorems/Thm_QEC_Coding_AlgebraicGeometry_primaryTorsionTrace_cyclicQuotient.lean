-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:38.549731+00:00
-- url     : https://prove2.me/theorems/f4b9d413-2740-4d25-b071-943f16461774
-- title:
--   Algebraic Geometry: primary Torsion Trace cyclic Quotient
-- statement:
--   On `R ⧸ (a)`, the primary trace of multiplication by `r` at an
--   irreducible `q` is the multiplicity of `q` in `a`, times `r mod q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L72-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L72-L85

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r)
        (multiplicity q a) =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
