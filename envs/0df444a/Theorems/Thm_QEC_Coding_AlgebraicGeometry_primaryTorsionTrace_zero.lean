-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_zero
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:10.906426+00:00
-- url     : https://prove2.me/theorems/c46a0001-7c72-4489-bd12-ba0950d7bea4
-- title:
--   Algebraic Geometry: primary Torsion Trace zero
-- statement:
--   The finite primary-torsion trace of the zero endomorphism is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Trace.lean#L87-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Trace.lean#L87-L99

import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_zero [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal] (n : ℕ) :
    primaryTorsionTrace p (0 : M →ₗ[R] M) n = 0 := by sorry
