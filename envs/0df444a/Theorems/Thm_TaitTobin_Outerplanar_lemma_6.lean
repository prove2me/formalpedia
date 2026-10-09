-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_lemma_6
-- name    : TaitTobin.Outerplanar.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:52.028665+00:00
-- url     : https://prove2.me/theorems/8e4e7ef9-414e-4aba-841c-7eb563ead977
-- title:
--   Lemma 6, p. 7 — the vertices B outside the closed neighbourhood of x carry eigenvector mass < C₂/√n
-- statement:
--   There are an absolute constant $C_2$ and a threshold $N$ such that the following holds for every $n \ge N$. Let $G$ be an outerplanar graph on $n$ vertices of maximum spectral radius $\lambda_1$ among outerplanar graphs on the same $n$ vertices, let $\mathbf v$ be a positive eigenvector for $\lambda_1$ normalized so that its maximum entry is $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. Put $B = V(G) \setminus (N(x) \cup \{x\})$, the vertices other than $x$ that are not adjacent to $x$. Then
--   $$\sum_{z \in B} \mathbf v_z < \frac{C_2}{\sqrt n}.$$
--
--   Together with Lemma 5 this shows that a vertex outside $N(x)\cup\{x\}$ has small eigenvector mass in its neighbourhood, which drives the edge-switching argument of Theorem 7.
--
--   **Formalization Note** The lemma is stated "for some absolute constant $C_2$"; its proof uses Lemma 5, which holds for $n$ sufficiently large, so the threshold $N$ carries over. $C_2$ is quantified before $N$ and the graph.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 7, Lemma 6

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Lemma 6, p. 7: there are an absolute constant `C₂` and a threshold `N` such that, for
`n ≥ N`, in an outerplanar graph on `n` vertices of maximum spectral radius, with Perron vector `v`
normalized to maximum entry `1` and `v x = 1`, the set `B = V(G) \ (N(x) ∪ {x})` satisfies
`∑_{z ∈ B} v_z < C₂/√n`. -/
theorem lemma_6 : ∃ C₂ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∑ z ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z), v z < C₂ / Real.sqrt n := by sorry
end TaitTobin.Outerplanar
