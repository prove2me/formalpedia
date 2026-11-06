-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_cyclicPowerFactorQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:42.612117+00:00
-- url     : https://prove2.me/theorems/2304d995-b293-4cd9-a96a-8e182e499f55
-- title:
--   Algebraic Geometry: primary Torsion Grade Trace cyclic Power Factor Quotient
-- statement:
--   Multiplication by `r` has trace `r mod q` on every one of the first `e`
--   primary grades of `R ⧸ (q ^ e * b)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L253-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L253-L291

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : b ≠ 0) (i : ℕ) (hi : i < e) (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i =
      Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
