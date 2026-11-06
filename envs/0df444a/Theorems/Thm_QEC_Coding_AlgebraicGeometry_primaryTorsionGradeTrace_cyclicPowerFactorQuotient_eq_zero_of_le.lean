-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:54.628238+00:00
-- url     : https://prove2.me/theorems/0e6c429e-98e7-48af-b0ae-a9542aaffb72
-- title:
--   Algebraic Geometry: primary Torsion Grade Trace cyclic Power Factor Quotient eq zero of le
-- statement:
--   Every primary-grade trace after the exact `q`-multiplicity is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L85-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean#L85-L105

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient_eq_zero_of_le
    [IsNoetherianRing R] (q : R) (hq : Prime q)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : ¬ q ∣ b) (i : ℕ) (hei : e ≤ i)
    (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i = 0 := by sorry
