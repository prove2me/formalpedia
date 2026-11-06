-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:48.067946+00:00
-- url     : https://prove2.me/theorems/dc1d9bbf-42a5-4f73-ba20-083dd9c4b1bd
-- title:
--   Algebraic Geometry: primary Torsion Trace cyclic Quotient of multiplicity le
-- statement:
--   At every depth bounding the multiplicity, the primary trace on a cyclic
--   quotient is the multiplicity times the reduced multiplier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L127-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L127-L151

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
    [IsNoetherianRing R] (q a r : R) (hq : Irreducible q)
    [hmax : (Ideal.span {q}).IsMaximal] (ha : a ≠ 0)
    (n : ℕ) (hqn : multiplicity q a ≤ n) :
    primaryTorsionTrace (Ideal.span {q}) (cyclicQuotientMul a r) n =
      (multiplicity q a : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
