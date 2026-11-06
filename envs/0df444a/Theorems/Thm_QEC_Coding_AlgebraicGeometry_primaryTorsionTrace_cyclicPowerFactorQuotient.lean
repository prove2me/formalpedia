-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cyclicPowerFactorQuotient
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicPowerFactorQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:59.619199+00:00
-- url     : https://prove2.me/theorems/fdc886ca-c2bb-45ca-b01f-000253eb92c0
-- title:
--   Algebraic Geometry: primary Torsion Trace cyclic Power Factor Quotient
-- statement:
--   The first `e` primary grades of multiplication by `r` on
--   `R ⧸ (q ^ e * b)` have total trace `e * (r mod q)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L295-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicFactorTrace.lean#L295-L315

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicPowerFactorQuotient
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : b ≠ 0) (r : R) :
    primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by sorry
