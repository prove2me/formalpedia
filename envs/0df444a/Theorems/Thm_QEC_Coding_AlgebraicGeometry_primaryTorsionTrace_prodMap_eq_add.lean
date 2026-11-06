-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_prodMap_eq_add
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_prodMap_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:48.699761+00:00
-- url     : https://prove2.me/theorems/182f74cc-9193-4ca7-9aac-0bb91f7f3541
-- title:
--   Algebraic Geometry: primary Torsion Trace prod Map eq add
-- statement:
--   Primary torsion trace is additive on a binary product endomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/ProdTrace.lean#L32-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/ProdTrace.lean#L32-L61

import Mathlib.LinearAlgebra.Prod
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_prodMap_eq_add
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (depth : ℕ) :
    primaryTorsionTrace p (f.prodMap g) depth =
      primaryTorsionTrace p f depth + primaryTorsionTrace p g depth := by sorry
