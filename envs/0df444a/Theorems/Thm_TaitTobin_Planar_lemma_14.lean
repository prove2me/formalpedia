-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_14
-- name    : TaitTobin.Planar.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:48:22.45915+00:00
-- url     : https://prove2.me/theorems/59acb78d-d771-488c-9b27-db3c45d30212
-- title:
--   Lemma 14, p. 12 — A is empty: every vertex other than x and w is adjacent to both
-- statement:
--   There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ and all sufficiently large $n$ the following holds. Let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $w$ any vertex as in Lemma 11. With $B = N(x) \cap N(w)$ and $A = V(G) \setminus (\{x, w\} \cup B)$,
--   $$A = \emptyset,$$
--   that is, every vertex $u \notin \{x, w\}$ is adjacent to both $x$ and $w$.
--
--   Hence $K_2 + I_{n-2}$ (an edge joined to an independent set of size $n-2$) is a spanning subgraph of the extremal graph.
--
--   **Formalization Note** The set $A$ is not defined in Lean; the statement is its unfolded form $\forall u \notin \{x,w\},\ u \sim x \wedge u \sim w$. The lemma is stated for every $w$ satisfying the conclusion of Lemma 11.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 12, Lemma 14 (A defined on p. 11)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 14, p. 12: for every sufficiently small `ε > 0` and all large `n`, in a planar graph of
maximum spectral radius, if `w` is a vertex as in Lemma 11 then the set
`A = V(G) \ ({x, w} ∪ (N(x) ∩ N(w)))` is empty: every vertex `u ∉ {x, w}` is adjacent to both
`x` and `w`. -/
theorem lemma_14 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w →
          ∀ u : Fin n, u ≠ x → u ≠ w → G.Adj u x ∧ G.Adj u w := by sorry
end TaitTobin.Planar
