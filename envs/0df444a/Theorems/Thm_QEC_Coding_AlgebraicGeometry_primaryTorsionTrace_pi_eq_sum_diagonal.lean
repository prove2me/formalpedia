-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_pi_eq_sum_diagonal
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_pi_eq_sum_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:32.277403+00:00
-- url     : https://prove2.me/theorems/764af823-18c0-43b6-9f53-ad230689b150
-- title:
--   Algebraic Geometry: primary Torsion Trace pi eq sum diagonal
-- statement:
--   The primary-torsion trace of an endomorphism of a finite product is the
--   sum of the primary traces of its diagonal coordinate blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PiTrace.lean#L68-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PiTrace.lean#L68-L99

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_pi_eq_sum_diagonal
    [IsNoetherianRing R] [∀ i, Module.Finite R (M i)]
    [Module.Finite R (∀ i, M i)]
    (p : Ideal R) [p.IsMaximal]
    (f : (∀ i, M i) →ₗ[R] ∀ i, M i) (n : ℕ) :
    primaryTorsionTrace (M := ∀ i, M i) p f n =
      ∑ i, primaryTorsionTrace (M := M i) p
        (piDiagonalBlock f i) n := by sorry
