-- Prove2me | Theorems.Thm_WeightedCoordGames_theorem_3
-- name    : WeightedCoordGames.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:44.979555+00:00
-- url     : https://prove2.me/theorems/39c26c11-1c02-455d-ab7b-1f0740f06021
-- title:
--   Theorem 3 — weighted simple cycles with at most one bonus node ensure improvement paths of length $\le 2n-1$
-- statement:
--   Let $n\ge 2$ and consider the weighted simple cycle $1\to2\to\dots\to n\to1$ with positive edge weights $w_{i\to i+1}>0$, a colour assignment with non-empty colour sets $C(i)$, and bonuses $\beta(i,c)\in\mathbb N$ such that at most one node has a non-zero bonus function. Then the coordination game ensures improvement paths of length
--   $$
--   \le 2n-1:
--   $$
--   from every joint strategy there is a sequence of at most $2n-1$ profitable unilateral deviations that ends in a Nash equilibrium.
--
--   Directed cycles do not have the finite improvement property (Example 2), so this is the strongest kind of convergence one can hope for. The construction behind it is reused for the first cycle of an open chain in Theorem 15.
--
--   **Formalization Note** Nodes are $0,\dots,n-1$ and the edges are $a\to a+1 \pmod n$.
--
--   Differences from the source:
--   - encoding: "ensures improvement paths of length ≤ 2n − 1" → a list $s_0,\dots,s_L$ with $L\le 2n-1$, each step a profitable deviation of one player and $s_L$ a Nash equilibrium; reason: the paper's definition (§2, p.8); a finite improvement path cannot be extended, i.e. ends in a Nash equilibrium, and its length counts deviations
--   - reading: number of players unstated in the theorem → $n\ge2$; reason: §2, p.7: "Throughout the paper n > 1 denotes the number of players"
--   - encoding: nodes $1,\dots,n$ and weights $w_e$ on the edges → `Fin n` (0-based) and a weight function on all ordered pairs, positive on the edges $a\to a+1$; reason: weights off the edges are never read; same instances
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §4, Theorem 3, p.11

import Mathlib
import Definitions.Def_WeightedCoordGames_Model

namespace WeightedCoordGames

/-- **Theorem 3** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §4, p.11). Every coordination game on
a weighted simple cycle in which at most one node has bonuses ensures improvement paths of
length `≤ 2n − 1`.

The cycle is `0 → 1 → … → n−1 → 0` on `Fin n` with `n ≥ 2` (§2: "Throughout the paper `n > 1`"),
every edge `a → a+1` has a positive weight, every colour set is non-empty, and all nodes other
than one node `i₀` have the constant bonus function `0`.

**Formalization Note.** Nodes are 0-based; the length of an improvement path is its number of
steps (`EnsuresImprovementPaths`). -/
theorem theorem_3 {M : Type*} [Fintype M] [DecidableEq M] (n : ℕ) (hn : 2 ≤ n)
    (w : Fin n → Fin n → ℝ) (hw : ∀ a : Fin n, 0 < w a (finRotate n a))
    (β : Fin n → M → ℕ) (hβ : ∃ i₀ : Fin n, ∀ i, i ≠ i₀ → ∀ c, β i c = 0)
    (C : Fin n → Finset M) (hC : ∀ i, (C i).Nonempty) :
    (cycleGame n w β C).toGame.EnsuresImprovementPaths (2 * n - 1) := by sorry

end WeightedCoordGames
