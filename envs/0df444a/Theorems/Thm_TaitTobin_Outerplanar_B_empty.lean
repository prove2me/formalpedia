-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_B_empty
-- name    : TaitTobin.Outerplanar.B_empty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:20.482683+00:00
-- url     : https://prove2.me/theorems/edfd2194-5b47-40b8-9432-d05ad428412b
-- title:
--   Proof of Theorem 7, p. 7 — for n large, B is empty: x is adjacent to every other vertex
-- statement:
--   There is a threshold $N$ such that the following holds for every $n \ge N$. Let $G$ be an outerplanar graph on $n$ vertices of maximum spectral radius $\lambda_1$ among outerplanar graphs on the same $n$ vertices, let $\mathbf v$ be a positive eigenvector for $\lambda_1$ normalized so that its maximum entry is $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. Then
--   $$B = V(G) \setminus (N(x) \cup \{x\}) = \emptyset,$$
--   that is, $x$ is adjacent to every other vertex of $G$.
--
--   This is the first step of the proof of Theorem 7; the rest of the proof is combinatorial.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 7, proof of Theorem 7, first paragraph

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Proof of Theorem 7, p. 7: for `n` large, in an outerplanar graph on `n` vertices of maximum
spectral radius the vertex `x` of Perron entry `1` is adjacent to every other vertex (`B = ∅`). -/
theorem B_empty : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ y : Fin n, y ≠ x → G.Adj x y := by sorry
end TaitTobin.Outerplanar
