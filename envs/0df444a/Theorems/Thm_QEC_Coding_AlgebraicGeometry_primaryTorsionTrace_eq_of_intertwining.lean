-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_eq_of_intertwining
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_eq_of_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:37.567274+00:00
-- url     : https://prove2.me/theorems/d7aabb75-f852-4f7f-86a1-1219eb6125c5
-- title:
--   Algebraic Geometry: primary Torsion Trace eq of intertwining
-- statement:
--   Intertwining endomorphisms have equal finite primary-torsion traces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L192-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L192-L200

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_eq_of_intertwining [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (n : ℕ) : primaryTorsionTrace p f n = primaryTorsionTrace p g n := by sorry
