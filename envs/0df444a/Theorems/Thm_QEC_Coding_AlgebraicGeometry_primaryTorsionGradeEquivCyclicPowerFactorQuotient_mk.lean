-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEquivCyclicPowerFactorQuotient_mk
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivCyclicPowerFactorQuotient_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:06.19817+00:00
-- url     : https://prove2.me/theorems/964f8c9a-2041-457a-9353-b32c05d86244
-- title:
--   Algebraic Geometry: primary Torsion Grade Equiv Cyclic Power Factor Quotient mk
-- statement:
--   On representatives, the cyclic-factor grade equivalence is scalar
--   multiplication of its distinguished grade generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L211-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L211-L228

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquivCyclicPowerFactorQuotient_mk
    (q : R) (hq : q ≠ 0) (e : ℕ) (b : R) (hb : b ≠ 0)
    (i : ℕ) (hi : i < e) (r : R) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e * b}) (Ideal.span {q}) i
    primaryTorsionGradeEquivCyclicPowerFactorQuotient
        q hq e b hb i hi (Ideal.Quotient.mk (Ideal.span {q}) r) =
      Ideal.Quotient.mk (Ideal.span {q}) r •
        primaryTorsionGradeEquivCyclicPowerFactorQuotient
          q hq e b hb i hi 1 := by sorry
