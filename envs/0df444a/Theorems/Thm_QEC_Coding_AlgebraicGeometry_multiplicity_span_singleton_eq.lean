-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_multiplicity_span_singleton_eq
-- name    : QEC.Coding.AlgebraicGeometry.multiplicity_span_singleton_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:28.883116+00:00
-- url     : https://prove2.me/theorems/f448c107-56ac-4fa0-af5b-d173dc00c19e
-- title:
--   Algebraic Geometry: multiplicity span singleton eq
-- statement:
--   In a principal ideal domain, the multiplicity of an irreducible element
--   in a nonzero element agrees with the multiplicity of their principal ideals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L39-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean#L39-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
variable [IsDomain R] [IsPrincipalIdealRing R]

theorem QEC.Coding.AlgebraicGeometry.multiplicity_span_singleton_eq (q a : R) (hq : Irreducible q)
    (ha : a ≠ 0) :
    multiplicity (Ideal.span {q}) (Ideal.span {a}) = multiplicity q a := by sorry
