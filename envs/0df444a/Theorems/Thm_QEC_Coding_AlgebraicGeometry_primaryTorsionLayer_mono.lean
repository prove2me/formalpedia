-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionLayer_mono
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionLayer_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:00.704195+00:00
-- url     : https://prove2.me/theorems/1ecfb3a2-62c6-4125-8201-5f71fde09b33
-- title:
--   Algebraic Geometry: primary Torsion Layer mono
-- statement:
--   The primary torsion layers form an increasing filtration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Grade.lean#L33-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Grade.lean#L33-L35

import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionLayer_mono (p : Ideal R) (i j : ℕ) (hij : i ≤ j) :
    primaryTorsionLayer p M i ≤ primaryTorsionLayer p M j := by sorry
