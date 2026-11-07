-- Prove2me | Theorems.Thm_TenChallenges_challenge_04
-- name    : TenChallenges.challenge_04
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:39:48.439461+00:00
-- url     : https://prove2.me/theorems/f8264a69-87c1-4284-b155-be21a37d4bab
-- title:
--   Sidorenko's conjecture
-- statement:
--   **Sidorenko's conjecture.** For every finite bipartite graph $H$ and every finite graph $G$ with at least one vertex, the homomorphism density of $H$ in $G$ is at least the edge density of $G$ raised to the number of edges of $H$:
--
--   $$t(H,G)\ \ge\ t(K_2,G)^{\,e(H)}.$$
--
--   Here $H$ is bipartite in the sense that its vertex set is the union of two disjoint sets $X$ and $Y$ with every edge joining $X$ to $Y$. The conjecture is equivalent to the statement $\mathrm{Sid}(r)$ for all $r$ of the scaled Challenge 4, since every finite bipartite graph has sides bounded by some $r$. It is known for all $H$ with at most four vertices on one side. In 2026 OpenAI announced a counterexample, with a Lean proof, for a bipartite $H$ on $35$ vertices with sides of size $13$ and $22$; if it stands, this statement is false and the mission closes by a disproof.
--
--   **Formalization Note.** Vertex types are finite types in the lowest universe, $G$ is nonempty, and bipartiteness is Mathlib's `IsBipartiteWith X Y` together with $X\cup Y=$ `Set.univ`, the same notion as in `BipartiteBoundedBy` without the size bounds.
-- source:
--   A. F. Sidorenko, A correlation inequality for bipartite graphs, Graphs Combin. 9 (1993), 201–204, https://doi.org/10.1007/BF02988307 (the conjecture); equivalent to the universal form of V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 4

import Definitions.Def_TenChallenges_Challenge_04
open SimpleGraph

namespace TenChallenges
theorem challenge_04 {W V : Type} [Fintype W] [Fintype V] [Nonempty V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hH : ∃ X Y : Set W, H.IsBipartiteWith X Y ∧ X ∪ Y = Set.univ) :
    SidorenkoFor H G := by sorry
end TenChallenges
