-- Prove2me | Theorems.Thm_WeightedCoordGames_mu_range
-- name    : WeightedCoordGames.mu_range
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:16.229712+00:00
-- url     : https://prove2.me/theorems/47262bb6-6f42-439c-95fd-1504839bb813
-- title:
--   §5, proof of Theorem 15, p.20 — range of the progress measure, $\mathrm{guard}(s)+1\le\mathrm{NBR}(s)\le|\mathrm{prefix}(s)|\le m$
-- statement:
--   Consider a coordination game on an open chain of $m$ cycles with non-empty colour sets, and a joint strategy $s$ that is not a Nash equilibrium. Then $\mathrm{guard}(s)\in\{0,\dots,m-1\}$ and
--   $$
--   \mathrm{guard}(s)+1\le\mathrm{NBR}(s)\le|\mathrm{prefix}(s)|\le m.
--   $$
--
--   Together with $\mu(s)=(m+1,0,0,0)$ at Nash equilibria, this bounds the number of values the progress measure $\mu$ can take, which is the counting step of the proof of Theorem 15.
--
--   Differences from the source:
--   - encoding: $\mathrm{guard}(s)\in\{0,\dots,m-1\}$ → `guard ≤ m - 1` in $\mathbb N$; reason: $m\ge2$, so there is no truncation
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, proof of Theorem 15, p.20 (second paragraph)

import Mathlib
import Definitions.Def_WeightedCoordGames_Model
import Definitions.Def_WeightedCoordGames_Algorithm

namespace WeightedCoordGames

/-- **The range of `µ`** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, proof of Theorem 15, p.20).
If the joint strategy `s` is not a Nash equilibrium, then `guard(s) ∈ {0, …, m − 1}` and
`guard(s) + 1 ≤ NBR(s) ≤ |prefix(s)| ≤ m`. -/
theorem mu_range {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty)
    (s : V → M) (hs : (chainGame O C).toGame.IsJoint s)
    (hne : ¬ (chainGame O C).toGame.IsNash s) :
    O.guard C s ≤ m - 1 ∧ O.guard C s + 1 ≤ O.nbr C s ∧
      O.nbr C s ≤ O.prefixLen C s ∧ O.prefixLen C s ≤ m := by sorry

end WeightedCoordGames
