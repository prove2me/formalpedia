-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_primePowerQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_primePowerQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:03.234456+00:00
-- url     : https://prove2.me/theorems/592f30fd-7d63-4762-abb6-3b10fe24c6e3
-- title:
--   Algebraic Geometry: primary Torsion Trace prime Power Quotient
-- statement:
--   The depth-`e` primary trace on `R ⧸ (q ^ e)` is `e` times reduction
--   modulo `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L272-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L272-L292

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_primePowerQuotient
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (r : R) :
    primaryTorsionTrace (Ideal.span {q})
        (primePowerQuotientMul q e r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
