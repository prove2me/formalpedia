-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_quotientMul_eq_add
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_quotientMul_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:48.227743+00:00
-- url     : https://prove2.me/theorems/b5ca98e1-d3a1-48cf-a7c2-1b7202db48c1
-- title:
--   Algebraic Geometry: primary Torsion Trace quotient Mul eq add
-- statement:
--   Chinese remaindering splits the primary trace of multiplication on a
--   coprime product quotient into the two coordinate primary traces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CRTTrace.lean#L68-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CRTTrace.lean#L68-L103

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_quotientMul_eq_add
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal]
    (I J : Ideal S) (hcop : IsCoprime I J)
    (b : S) (depth : ℕ) :
    primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ (I * J)) (Ideal.Quotient.mk (I * J) b)) depth =
      primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)) depth +
        primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ J) (Ideal.Quotient.mk J b)) depth := by sorry
