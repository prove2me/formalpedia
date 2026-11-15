-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_infiniteCore
-- name    : TenChallenges.challenge_10_infiniteCore
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T21:50:59.225201+00:00
-- url     : https://prove2.me/theorems/f4e6a747-6031-49ad-ae8e-1918803ca4eb
-- title:
--   Challenge 10: every ordinal clock for an infinite-minimum-degree core with finitely many outside hubs
-- statement:
--   Let $G=(V,E)$ be a countable simple graph and let $R\subseteq V$ be a subset of vertices such that:
--
--   1. Every vertex $x\in R$ has infinitely many neighbors inside $R$, i.e., $|N_G(x)\cap R| = \infty$.
--   2. Only finitely many vertices outside $R$ have infinite degree in $G$:
--
--   $$|\{x\in V\setminus R : \deg_G(x)=\infty\}| < \infty.$$
--
--   Then Partitioner has a winning strategy in the unfriendly partitioning game on $G$ starting from the empty partial coloring at every ordinal clock:
--
--   $$\forall \alpha\in\mathrm{Ord},\quad \operatorname{PartitionerWins}(G,\varnothing,\alpha).$$
--
--   At each move, Challenger announces a vertex $v\in V$ and a strictly smaller ordinal clock $\beta<\alpha$, and Partitioner responds with a finite partial coloring extending the current position so that $v$ has at least as many opposite-colored neighbors as same-colored neighbors.
--
--   This unifies and strictly generalizes two classical regimes of the Unfriendly Partition Problem: taking $R=\varnothing$ recovers the Aharoni-Milner-Prikry theorem for countable graphs with finitely many infinite-degree vertices, while taking $R=V$ recovers countable graphs of infinite minimum degree, and intermediate choices allow an infinite-minimum-degree core attached arbitrarily to infinite locally-finite subgraphs and finitely many exceptional hubs.
--
--   **Formalization Note.** The core condition and outside-hub finiteness are expressed via `(G.neighborSet x ∩ R).Infinite` and `{x : V | x ∉ R ∧ (G.neighborSet x).Infinite}.Finite`. The vertex universe `u` and clock universe `v` are independent, using `PartitionerWins` and `emptyPartition` from `Definitions.Def_TenChallenges_Challenge_10`.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (Unfriendly Partitioning Game), https://tenchallenges.github.io/ten-challenges/ ; generalizes R. Aharoni, E. C. Milner, and K. Prikry, Unfriendly partitions of a graph, J. Combin. Theory Ser. B 50 (1990), 1-10, Theorem 1, https://doi.org/10.1016/0095-8956(90)90092-E, and the finite-repair method in L. Aurichi and L. Real, Remarks on the countable case of the Unfriendly Partition Problem, Lemma 2.1, https://arxiv.org/abs/2412.14151.

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10_infiniteCore {V : Type u} [Countable V] (G : SimpleGraph V)
    (R : Set V) (hR : ∀ x ∈ R, (G.neighborSet x ∩ R).Infinite)
    (hOutside : {x : V | x ∉ R ∧ (G.neighborSet x).Infinite}.Finite)
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
