-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_rank_additive_of_subsets
-- name    : WhitneyMatroid.Components.rank_additive_of_subsets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:55.029554+00:00
-- url     : https://prove2.me/theorems/078810a2-cced-4ff3-b261-8e7e4251f434
-- title:
--   Theorem 11 — rank additivity passes to subsets of the two parts
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$ with rank function $r$, and let $M_1, M_2\subseteq E$ with
--
--   $$
--   r(M_1 + M_2) = r(M_1) + r(M_2).
--   $$
--
--   If $M_1'\subseteq M_1$ and $M_2'\subseteq M_2$, then
--
--   $$
--   r(M_1' + M_2') = r(M_1') + r(M_2').
--   $$
--
--   Here $+$ denotes the union of sets. In words: if the rank of a union is the sum of the ranks of the two parts, the same holds for any choice of subsets of the two parts. This is the basic tool behind Theorems 12–19.
--
--   **Formalization Note** Whitney states the theorem for a matroid $M = M_1 + M_2$; here $M_1$ and $M_2$ are arbitrary subsets of the ground set of an ambient finite matroid, which is the same statement applied to the submatroid $M_1+M_2$ (rank in a submatroid is the induced rank). The parts are not required to be disjoint; Whitney writes $M_1+M_2$ also for overlapping sets (Theorem 13), and the statement holds in that generality. Ranks are Mathlib's `M.eRk`, finite here.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 518, Theorem 11

import Mathlib

namespace WhitneyMatroid.Components

theorem rank_additive_of_subsets {α : Type*} (M : Matroid α) [M.Finite]
    (M₁ M₂ M₁' M₂' : Set α) (hM₁ : M₁ ⊆ M.E) (hM₂ : M₂ ⊆ M.E)
    (hr : M.eRk (M₁ ∪ M₂) = M.eRk M₁ + M.eRk M₂)
    (h₁ : M₁' ⊆ M₁) (h₂ : M₂' ⊆ M₂) :
    M.eRk (M₁' ∪ M₂') = M.eRk M₁' + M.eRk M₂' := by sorry

end WhitneyMatroid.Components
