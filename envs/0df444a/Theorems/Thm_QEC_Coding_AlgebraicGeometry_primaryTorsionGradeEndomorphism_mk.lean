-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEndomorphism_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:25.78473+00:00
-- url     : https://prove2.me/theorems/bfa4a18e-ce7f-4e0d-a2f6-b09558e07f9a
-- title:
--   Algebraic Geometry: primary Torsion Grade Endomorphism mk
-- statement:
--   On a quotient representative, the induced grade endomorphism is the
--   class of the restricted original endomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Grade.lean#L132-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Grade.lean#L132-L139

import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEndomorphism_mk (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p f i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (primaryTorsionLayerEndomorphism p f (i + 1) x) := by sorry
