-- Prove2me | Theorems.Thm_WeightedCoordGames_theorem_7
-- name    : WeightedCoordGames.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:56.74097+00:00
-- url     : https://prove2.me/theorems/a5ed1791-39ca-40d8-a1d0-d45ffacfbc61
-- title:
--   Theorem 7 — weighted simple cycles with two bonus nodes ensure improvement paths of length $\le 3n$
-- statement:
--   Let $n\ge 2$ and consider the weighted simple cycle $1\to2\to\dots\to n\to1$ with positive edge weights, a colour assignment with non-empty colour sets $C(i)$, and bonuses $\beta(i,c)\in\mathbb N$ such that all nodes other than two nodes $i_1,i_2$ have zero bonuses. Then the coordination game ensures improvement paths of length
--   $$
--   \le 3n.
--   $$
--
--   Example 6 shows that with three bonus nodes and non-trivial weights a Nash equilibrium need not exist, so two bonus nodes is the limit for this kind of result. In an open chain each cycle, seen from the outside, carries at most two bonus nodes (its link nodes), which is why this construction drives Theorem 15.
--
--   **Formalization Note** Nodes are $0,\dots,n-1$ and the edges are $a\to a+1\pmod n$.
--
--   Differences from the source:
--   - generalization: "two nodes have bonuses" → at most two nodes $i_1,i_2$ (possibly equal) have non-zero bonuses; reason: contains the printed case; with at most one bonus node Theorem 3 gives the smaller bound $2n-1\le 3n$, and §5 applies this construction to cycles with one bonus node (Appendix, p.37)
--   - encoding: "ensures improvement paths of length ≤ 3n" → a list $s_0,\dots,s_L$ with $L\le 3n$, each step a profitable deviation of one player and $s_L$ a Nash equilibrium; reason: the paper's definition (§2, p.8)
--   - reading: number of players unstated in the theorem → $n\ge2$; reason: §2, p.7: "Throughout the paper n > 1 denotes the number of players"
--   - encoding: nodes $1,\dots,n$ and weights $w_e$ on the edges → `Fin n` (0-based) and a weight function on all ordered pairs, positive on the edges; reason: weights off the edges are never read; same instances
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §4, Theorem 7, p.13 (proof pp.13–14)

import Mathlib
import Definitions.Def_WeightedCoordGames_Model

namespace WeightedCoordGames

/-- **Theorem 7** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §4, p.13; proof pp.13–14). Every
coordination game on a weighted simple cycle in which two nodes have bonuses ensures improvement
paths of length `≤ 3n`.

The cycle is `0 → 1 → … → n−1 → 0` on `Fin n` with `n ≥ 2`, every edge `a → a+1` has a positive
weight, every colour set is non-empty, and all nodes other than two nodes `i₁, i₂` have the
constant bonus function `0`.

**Formalization Note.** "Two nodes have bonuses" is stated as "at most two nodes have bonuses"
(`i₁ = i₂` and nodes among `i₁, i₂` with zero bonuses are allowed); this contains the printed
statement. Nodes are 0-based; length counts steps. -/
theorem theorem_7 {M : Type*} [Fintype M] [DecidableEq M] (n : ℕ) (hn : 2 ≤ n)
    (w : Fin n → Fin n → ℝ) (hw : ∀ a : Fin n, 0 < w a (finRotate n a))
    (β : Fin n → M → ℕ) (hβ : ∃ i₁ i₂ : Fin n, ∀ i, i ≠ i₁ → i ≠ i₂ → ∀ c, β i c = 0)
    (C : Fin n → Finset M) (hC : ∀ i, (C i).Nonempty) :
    (cycleGame n w β C).toGame.EnsuresImprovementPaths (3 * n) := by sorry

end WeightedCoordGames
