-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_adj_entry_one
-- name    : TaitTobin.Irregularity.adj_entry_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:32.510978+00:00
-- url     : https://prove2.me/theorems/70d0ccb6-8771-4c50-81a7-5d3ac0c9908b
-- title:
--   Proof of Proposition 20, p. 18 (corrected) — every vertex other than a lone vertex of entry 1 is adjacent to a vertex of entry 1
-- statement:
--   There is $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, and let $\mathbf v$ be a leading eigenvector with positive entries and maximum entry $1$. Then every vertex $u$ such that some other vertex has entry $1$ (in particular every $u$ with $\mathbf v_u < 1$) has a neighbour $w$ with $\mathbf v_w = 1$:
--   $$\bigl(\exists\, w' \ne u,\ \mathbf v_{w'} = 1\bigr) \implies \exists\, w \sim u,\ \mathbf v_w = 1 .$$
--
--   Consequently the edges at vertices of entry $1$ span all vertices, so deleting an edge not incident to such a vertex never disconnects $G$; Proposition 20's proof uses this repeatedly when it applies Lemma 19.
--
--   **Formalization Note** The page says "every vertex in $G$". For a vertex of entry $1$ that is false in general: the extremal graph is a pineapple whose hub is the unique vertex of entry $1$, and the hub has no neighbour of entry $1$. The statement excludes only that case, a vertex that is the unique vertex of entry $1$: every vertex of entry less than $1$ is covered (the proof's edge switch), and so is every vertex of entry $1$ when another vertex has entry $1$ (by Lemma 19, as the page's preceding sentence says).
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 18, proof of Proposition 20, second sentence, corrected

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Proof of Proposition 20, p. 18, corrected: for `n` large, in a maximizer `G` of `λ₁ − d` with
Perron vector `v` (maximum entry `1`), every vertex `u` other than a lone vertex of entry `1`
(i.e. every `u` such that some vertex `w ≠ u` has entry `1`) is adjacent to a vertex of entry `1`.
(The page says "every vertex"; the only vertex of entry `1` has no neighbour of entry `1`, e.g. the
hub of a pineapple.) -/
theorem adj_entry_one : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → (∃ x : Fin n, v x = 1) →
      ∀ u : Fin n, (∃ w : Fin n, w ≠ u ∧ v w = 1) → ∃ w : Fin n, G.Adj u w ∧ v w = 1 := by sorry
end TaitTobin.Irregularity
