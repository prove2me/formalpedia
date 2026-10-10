-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_rows_determine_all
-- name    : WeilDefect.MarkerStability.finite_sampling_rows_determine_all
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:05:07.106306+00:00
-- url     : https://prove2.me/theorems/d0039084-1466-457e-992c-150ad57ce609
-- title:
--   A finite-dimensional row family has one bounded sampling set for every coefficient vector
-- statement:
--   Let $I$ be a finite index set and let $r_\rho\in\mathbb C^I$ be ANY family of rows, indexed by an arbitrary set $\Omega$. There is ONE finite subset $G\subseteq\Omega$, of size at most $|I|$, such that for EVERY coefficient vector $c\in\mathbb C^I$, $$\bigl(\forall\rho\in G,\ r_\rho\cdot c=0\bigr)\iff\bigl(\forall\rho\in\Omega,\ r_\rho\cdot c=0\bigr).$$ The same $G$ is chosen before $c$. No injectivity, independence of the full row family, enumeration, finiteness of $\Omega$, or nonzero common-kernel assertion is assumed.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/FiniteSampling.lean, exact declaration WeilDefect.MarkerStability.finite_sampling_rows_determine_all, compiling source a5af8470c9220c0783752dac5c5a25fc842dbe0d

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
open Matrix
open scoped BigOperators Classical
noncomputable section

theorem WeilDefect.MarkerStability.finite_sampling_rows_determine_all
    {I Ω : Type*} [Fintype I] (r : Ω → (I → ℂ)) :
    ∃ G : Finset Ω, G.card ≤ Fintype.card I ∧
      ∀ c : I → ℂ, (∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0 := by sorry
