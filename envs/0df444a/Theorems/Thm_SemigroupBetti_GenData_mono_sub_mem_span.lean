-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mono_sub_mem_span
-- name    : SemigroupBetti.GenData.mono_sub_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:26.408788+00:00
-- url     : https://prove2.me/theorems/08a4a03d-5eb2-4245-97e7-c569363da2b6
-- title:
--   Gen Data: mono sub mem span
-- statement:
--   **Lemma 0 (B–F), binomial form.** Every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in
--   the ideal spanned by the chosen binomials.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L202-L228
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L202-L228

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.mono_sub_mem_span (d : ℕ) : ∀ z z' : Fin 4 → ℕ, G.nu z = d → G.nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (G.binomGens K : Set _) := by sorry
