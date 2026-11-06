-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_comp_comm
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_comp_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:50.162145+00:00
-- url     : https://prove2.me/theorems/e87f49eb-b501-478e-aefe-a225e862817b
-- title:
--   Algebraic Geometry: primary Torsion Trace comp comm
-- statement:
--   The finite primary-torsion trace is cyclic for a composite through
--   another finite module.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L174-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L174-L183

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_comp_comm [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (g.comp f) n =
      primaryTorsionTrace p (f.comp g) n := by sorry
