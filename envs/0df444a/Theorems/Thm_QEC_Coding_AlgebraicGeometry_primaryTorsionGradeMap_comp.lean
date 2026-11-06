-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeMap_comp
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:09.654964+00:00
-- url     : https://prove2.me/theorems/bebb697a-3872-43e7-b893-c6e04d15fbef
-- title:
--   Algebraic Geometry: primary Torsion Grade Map comp
-- statement:
--   Passing to a primary-torsion grade preserves composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L112-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L112-L131

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_comp
    {P : Type*} [AddCommGroup P] [Module R P]
    (p : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    letI := primaryTorsionGradeModule (M := P) p i
    primaryTorsionGradeMap p (g.comp f) i =
      (primaryTorsionGradeMap p g i).comp
        (primaryTorsionGradeMap p f i) := by sorry
