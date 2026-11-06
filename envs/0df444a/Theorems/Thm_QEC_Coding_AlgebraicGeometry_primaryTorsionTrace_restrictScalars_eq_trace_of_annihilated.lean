-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:28.654211+00:00
-- url     : https://prove2.me/theorems/aeb7667d-d302-4ff5-bdb6-f36ed98133be
-- title:
--   Algebraic Geometry: primary Torsion Trace restrict Scalars eq trace of annihilated
-- statement:
--   If `p` annihilates `M`, then at every positive depth the primary trace
--   of the restriction of a quotient-field-linear endomorphism is its ordinary
--   linear trace over `R ⧸ p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/AnnihilatedTrace.lean#L142-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/AnnihilatedTrace.lean#L142-L161

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_AnnihilatedTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    (hM : Module.IsTorsionBySet R M p)
    [Module (R ⧸ p) M] [IsScalarTower R (R ⧸ p) M]
    (f : M →ₗ[R ⧸ p] M) (n : ℕ) (hn : 0 < n) :
    primaryTorsionTrace p (f.restrictScalars R) n =
      LinearMap.trace (R ⧸ p) M f := by sorry
