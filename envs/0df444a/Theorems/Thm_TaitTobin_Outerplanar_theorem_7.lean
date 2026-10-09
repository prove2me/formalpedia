-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_theorem_7
-- name    : TaitTobin.Outerplanar.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:13.338387+00:00
-- url     : https://prove2.me/theorems/db58bfc9-32c8-43f6-9a92-18b986e69ef8
-- title:
--   Theorem 7, p. 7 — for large n, K₁ + Pₙ₋₁ is the unique outerplanar graph on n vertices of maximum spectral radius
-- statement:
--   There is a threshold $N$ such that for every $n \ge N$ and every graph $G$ on $n$ vertices the following are equivalent:
--
--   1. $G$ is outerplanar and its spectral radius $\lambda_1(G)$ (the largest eigenvalue of its adjacency matrix) is maximum among all outerplanar graphs on the same $n$ vertices;
--   2. $G$ is isomorphic to the fan $K_1 + P_{n-1}$, the join of a single vertex with a path on $n-1$ vertices.
--
--   In short,
--   $$\operatorname*{arg\,max}\{\lambda_1(G) : G \text{ outerplanar on } n \text{ vertices}\} = \{K_1 + P_{n-1}\} \text{ up to isomorphism}, \qquad n \ge N.$$
--
--   This proves, for all sufficiently large $n$, the conjecture of Cvetković and Rowlinson (1990) that the outerplanar graph on $n$ vertices of maximum spectral radius is $K_1 + P_{n-1}$.
--
--   **Formalization Note** The paper states the forward direction ("$G$ is the graph $K_1 + P_{n-1}$" for the maximizer $G$). The converse records that $K_1+P_{n-1}$ is *the* maximizer, as in Conjecture 2; it follows from the forward direction because a maximizer exists among the finitely many graphs on $n$ vertices and both outerplanarity and $\lambda_1$ are invariant under isomorphism. "Is the graph" is an isomorphism, not equality of labelled graphs. Outerplanarity is the topological notion (a plane drawing with every vertex on the outer face).
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 7, Theorem 7 (Conjecture 2, p. 1)

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Theorem 7, p. 7: for all sufficiently large `n`, an outerplanar graph on `n` vertices has
maximum spectral radius among outerplanar graphs on `n` vertices if and only if it is isomorphic to
`K₁ + Pₙ₋₁`. -/
theorem theorem_7 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G ↔ Nonempty (G ≃g fan n) := by sorry
end TaitTobin.Outerplanar
