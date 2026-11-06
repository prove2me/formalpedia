-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_primePowerQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_primePowerQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:21.250036+00:00
-- url     : https://prove2.me/theorems/96572e99-9f8e-4c91-8d89-fd9b520a2fe1
-- title:
--   Algebraic Geometry: primary Torsion Grade Trace prime Power Quotient
-- statement:
--   Multiplication by `r` has residue `r mod q` as its trace on every
--   nonzero primary grade of `R ⧸ (q ^ e)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L232-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L232-L268

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_primePowerQuotient
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e i : ℕ) (hi : i < e) (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (primePowerQuotientMul q e r) i =
      Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
