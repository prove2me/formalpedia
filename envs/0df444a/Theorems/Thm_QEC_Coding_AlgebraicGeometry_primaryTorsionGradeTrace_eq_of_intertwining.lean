-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_eq_of_intertwining
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_eq_of_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:25.476227+00:00
-- url     : https://prove2.me/theorems/f7cae299-f066-4209-9382-1ff3c95c5d60
-- title:
--   Algebraic Geometry: primary Torsion Grade Trace eq of intertwining
-- statement:
--   Intertwining endomorphisms have equal traces on every successive
--   primary-torsion grade.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L161-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L161-L189

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_eq_of_intertwining [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (i : ℕ) :
    primaryTorsionGradeTrace p f i = primaryTorsionGradeTrace p g i := by sorry
