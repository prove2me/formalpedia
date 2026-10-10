-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_modulo_submodule
-- name    : WeilDefect.MarkerStability.finite_functionals_modulo_submodule
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T18:15:29.453986+00:00
-- url     : https://prove2.me/theorems/fe8dc206-217b-4817-a203-ef70957bfcae
-- title:
--   Original functionals vanishing on a submodule admit quotient-dimension sampling
-- statement:
--   Let $V$ be a finite-dimensional complex vector space and let $W$ be a submodule on which every supplied original functional vanishes. ONE finite set $G$ of original indices, with $|G|\le\dim(V/W)$, determines vanishing of the entire original functional family for EVERY $v\in V$. This set is chosen before the vector. The vanishing hypothesis explicitly licenses quotient descent. No injectivity or algorithm is asserted.
-- source:
--   monocap-tech/weil, compiling source 2aef23a3fe056f7d73b4b52a6baf35b6453d9b0b, exact declaration WeilDefect.MarkerStability.finite_functionals_modulo_submodule

import Mathlib.Data.Complex.Basic
import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.finite_functionals_modulo_submodule
    {V Ω : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Submodule ℂ V) (r : Ω → Module.Dual ℂ V)
    (hr : ∀ ρ, W ≤ LinearMap.ker (r ρ)) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ (V ⧸ W) ∧
      ∀ v : V, (∀ ρ ∈ G, r ρ v = 0) ↔ ∀ ρ : Ω, r ρ v = 0 := by sorry
