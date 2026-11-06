-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_comp_comm
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_comp_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:20.294205+00:00
-- url     : https://prove2.me/theorems/a22faacb-7453-4d06-bc66-b75cf3d048e8
-- title:
--   Algebraic Geometry: primary Torsion Grade Trace comp comm
-- statement:
--   The trace on one primary-torsion grade is cyclic for a composite through
--   another finite module.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L149-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L149-L170

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_comp_comm [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (i : ℕ) :
    primaryTorsionGradeTrace p (g.comp f) i =
      primaryTorsionGradeTrace p (f.comp g) i := by sorry
