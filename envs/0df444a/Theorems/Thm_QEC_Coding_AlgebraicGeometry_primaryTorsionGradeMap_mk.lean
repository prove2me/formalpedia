-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeMap_mk
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:33:53.076705+00:00
-- url     : https://prove2.me/theorems/1ccb504b-8c9c-4196-8ee0-49432a78b12c
-- title:
--   Algebraic Geometry: primary Torsion Grade Map mk
-- statement:
--   The induced grade map sends a quotient representative to the class of
--   its image in the target torsion layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L103-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean#L103-L109

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_mk (p : Ideal R) (f : M →ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeMap p f i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerMap p f (i + 1) x) := by sorry
