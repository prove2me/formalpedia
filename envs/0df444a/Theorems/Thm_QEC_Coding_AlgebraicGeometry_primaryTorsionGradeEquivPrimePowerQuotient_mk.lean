-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEquivPrimePowerQuotient_mk
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivPrimePowerQuotient_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:00.657203+00:00
-- url     : https://prove2.me/theorems/0e97748d-d4aa-4a27-9688-88ebc86a5c7a
-- title:
--   Algebraic Geometry: primary Torsion Grade Equiv Prime Power Quotient mk
-- statement:
--   On a quotient representative, the prime-power grade equivalence is
--   scalar multiplication of the distinguished grade generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L193-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PrimePowerTrace.lean#L193-L208

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivPrimePowerQuotient_mk
    (q : R) (hq : q ≠ 0) (e i : ℕ) (hi : i < e) (r : R) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
    primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi
        (Ideal.Quotient.mk (Ideal.span {q}) r) =
      Ideal.Quotient.mk (Ideal.span {q}) r •
        primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi 1 := by sorry
