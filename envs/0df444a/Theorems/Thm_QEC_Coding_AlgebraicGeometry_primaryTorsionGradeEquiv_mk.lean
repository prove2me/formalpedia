-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEquiv_mk
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:26.852803+00:00
-- url     : https://prove2.me/theorems/56fdb39e-7f1c-4952-93d2-1311a5588bb8
-- title:
--   Algebraic Geometry: primary Torsion Grade Equiv mk
-- statement:
--   The induced grade equivalence sends a quotient representative to the
--   class of its image in the target torsion layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L129-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean#L129-L135

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquiv_mk (p : Ideal R) (e : M ≃ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeEquiv p e i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerEquiv p e (i + 1) x) := by sorry
