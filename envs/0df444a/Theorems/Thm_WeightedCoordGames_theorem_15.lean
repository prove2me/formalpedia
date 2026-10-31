-- Prove2me | Theorems.Thm_WeightedCoordGames_theorem_15
-- name    : WeightedCoordGames.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:01.442795+00:00
-- url     : https://prove2.me/theorems/9f6b4d06-8e60-4e28-bf3d-07f935b89f6e
-- title:
--   Theorem 15 — coordination games on an open chain of $m$ cycles of $v$ nodes ensure improvement paths of length $\le 3vm^3$
-- statement:
--   Let $\mathcal C_1,\dots,\mathcal C_m$ be an open chain of $m\ge2$ simple cycles, each with $v\ge3$ nodes. Here $[j,1]=[j+1,k_j]$ for $j\le m-1$, with arbitrary attachment positions $k_j\in\{2,\dots,v\}$. Let $M$ be any finite set of colours and $C$ any colour assignment with non-empty colour sets. Then the coordination game on the chain (unweighted, without bonuses) ensures improvement paths of length
--   $$
--   \le 3vm^3:
--   $$
--   from every joint strategy there is a sequence of at most $3vm^3$ profitable unilateral deviations that ends in a Nash equilibrium.
--
--   Open chains of cycles model ring-based network protection schemes. Even on a single directed cycle, improvement dynamics can cycle forever (Example 2), so the existence of short improvement paths from every starting point is the right notion of convergence here. The result gives a polynomial bound in both the cycle length and the number of cycles.
--
--   **Formalization Note** The standing assumptions $m\ge2$, $v\ge3$ of §5 are fields of the open-chain structure. Length counts deviations.
--
--   Differences from the source:
--   - encoding: "ensures improvement paths of length ≤ 3vm³" → a list $s_0,\dots,s_L$ with $L\le 3vm^3$, each step a profitable deviation of one player and $s_L$ a Nash equilibrium; reason: the paper's definition (§2, p.8); a finite improvement path cannot be extended, i.e. ends in a Nash equilibrium, and its length counts deviations
--   - reading: the theorem does not repeat the sizes → $m\ge2$ cycles, each with $v\ge3$ nodes; reason: §5 preamble, p.15: "an open chain of m ≥ 2 simple cycles … as long as each cycle has at least 3 nodes"
--   - reading: weights and bonuses not mentioned → unweighted, no bonuses; reason: §3, p.9 ("bonuses are assumed to be not present … unless explicitly stated otherwise"; unweighted graphs drop the qualification) and Table 1, p.6
--   - encoding: nodes $[j,i]$, $j\in\{1,\dots,m\}$, $i\in\{1,\dots,v\}$, and $k_j\in\{2,\dots,v\}$ → a vertex type with a surjective naming map `node : Fin m → Fin v → V` (0-based) and `k j ≠ 0`, two names denoting the same vertex exactly for the link identifications; reason: same graphs
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, Theorem 15, p.20 (proof §5 pp.15–20, Appendix pp.35–39)

import Mathlib
import Definitions.Def_WeightedCoordGames_Model

namespace WeightedCoordGames

/-- **Theorem 15** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, p.20; proof pp.15–20 and
Appendix pp.35–39). Every coordination game on an open chain of `m` cycles, each with `v` nodes,
ensures improvement paths of length `≤ 3vm³`.

For every open chain `O` of `m ≥ 2` cycles with `v ≥ 3` nodes each (every choice of the
attachment positions `k_j`), every finite set of colours `M` and every colour assignment `C` with
non-empty colour sets, the (unweighted, bonus-free) coordination game on `O` has, from every
joint strategy, an improvement path of at most `3vm³` steps that ends in a Nash equilibrium.

**Formalization Note.** `m ≥ 2` and `v ≥ 3` are fields of `OpenChain` (the standing assumptions
of §5, p.15). The length of an improvement path is its number of steps. -/
theorem theorem_15 {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty) :
    (chainGame O C).toGame.EnsuresImprovementPaths (3 * v * m ^ 3) := by sorry

end WeightedCoordGames
