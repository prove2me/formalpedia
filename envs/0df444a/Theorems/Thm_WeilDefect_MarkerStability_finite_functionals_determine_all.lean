-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
-- name    : WeilDefect.MarkerStability.finite_functionals_determine_all
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:25:55.912022+00:00
-- url     : https://prove2.me/theorems/0c3aba7e-76ba-4a81-b7a6-dfb63e2eccab
-- title:
--   One bounded sampling set determines a finite-dimensional functional family
-- statement:
--   For an arbitrary family of complex linear functionals on a finite-dimensional complex vector space $V$, ONE finite subset $G$ of the ORIGINAL indices, of size at most $\dim V$, determines their common kernel for EVERY vector. The same $G$ is chosen before the vector. No independence, injectivity, finite index family or algorithm is assumed.
-- source:
--   monocap-tech/weil, compiling source ae5ede91582c6434b1676f98d416b23316942daa, exact declaration WeilDefect.MarkerStability.finite_functionals_determine_all

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section

theorem WeilDefect.MarkerStability.finite_functionals_determine_all
    {V Ω : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (r : Ω → Module.Dual ℂ V) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ V ∧
      ∀ v : V, (∀ ρ ∈ G, r ρ v = 0) ↔ ∀ ρ : Ω, r ρ v = 0 := by sorry
