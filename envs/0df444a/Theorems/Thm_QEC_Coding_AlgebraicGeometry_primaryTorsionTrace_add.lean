-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_add
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:55.712631+00:00
-- url     : https://prove2.me/theorems/4d17e3b1-7cb6-4bc9-a2cd-f88f42a28e52
-- title:
--   Algebraic Geometry: primary Torsion Trace add
-- statement:
--   The finite primary-torsion trace is additive in the endomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Trace.lean#L102-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Trace.lean#L102-L117

import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_add [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f g : M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (f + g) n =
      primaryTorsionTrace p f n + primaryTorsionTrace p g n := by sorry
