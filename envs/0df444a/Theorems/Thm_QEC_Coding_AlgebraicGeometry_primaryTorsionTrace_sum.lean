-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_sum
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:19.872375+00:00
-- url     : https://prove2.me/theorems/75f1f784-dee1-4d6b-af9d-2d4b374589f2
-- title:
--   Algebraic Geometry: primary Torsion Trace sum
-- statement:
--   The finite primary-torsion trace is additive over a finite sum of
--   endomorphisms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PiTrace.lean#L30-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PiTrace.lean#L30-L43

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_sum
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    {ι : Type w} (s : Finset ι) (f : ι → M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (∑ i ∈ s, f i) n =
      ∑ i ∈ s, primaryTorsionTrace p (f i) n := by sorry
