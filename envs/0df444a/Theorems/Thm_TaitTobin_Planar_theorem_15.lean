-- Prove2me | Theorems.Thm_TaitTobin_Planar_theorem_15
-- name    : TaitTobin.Planar.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:42.736226+00:00
-- url     : https://prove2.me/theorems/804f70e6-789e-4b20-9add-3fb76b790c68
-- title:
--   Theorem 15 — for n ≥ N₀ the unique planar graph on n vertices with maximum spectral radius is K₂ + Pₙ₋₂
-- statement:
--   There is $N_0$ such that for every $n \ge N_0$ and every graph $G$ on $n$ vertices:
--   $$G \text{ is planar and } \lambda_1(G) = \max\{\lambda_1(G') : G' \text{ planar on } n \text{ vertices}\} \iff G \cong K_2 + P_{n-2}.$$
--
--   Here $\lambda_1$ is the largest adjacency eigenvalue and $K_2 + P_{n-2}$ is the join of an edge with a path on $n-2$ vertices. This settles, for all sufficiently large $n$, the conjecture of Boots and Royle (1991) and of Cao and Vince (1993) that the planar graph on $n \ge 9$ vertices of maximum spectral radius is $P_2 + P_{n-2}$; the conjecture fails for $n \in \{7, 8\}$.
--
--   **Formalization Note** "The unique planar graph … is $K_2 + P_{n-2}$" is stated as an equivalence: the forward direction says every maximizer is isomorphic to $K_2 + P_{n-2}$, the reverse that $K_2 + P_{n-2}$ is planar and attains the maximum. The threshold $N_0$ is unspecified, as in the paper; it is not $9$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 13, Theorem 15 (Conjecture 1, p. 1)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Theorem 15, p. 13: for all sufficiently large `n`, a graph on `n` vertices is planar with
maximum spectral radius among planar graphs on `n` vertices if and only if it is isomorphic to
`K₂ + Pₙ₋₂`. -/
theorem theorem_15 : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G ↔ Nonempty (G ≃g bookPath n) := by sorry
end TaitTobin.Planar
