-- Prove2me | Theorems.Thm_RobersonCx_splitB_cubic_bipartite_connected
-- name    : RobersonCx.splitB_cubic_bipartite_connected
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:24.54581+00:00
-- url     : https://prove2.me/theorems/e2b3ddb3-2711-4339-b476-9e026774581c
-- title:
--   §4.1 — $B^{(r)}_n$ is cubic, bipartite, and connected via a Hamilton cycle of spokes and short edges
-- statement:
--   Let $r\ge2$ and $n>2r$. The graph $B^{(r)}_n$ is simple, cubic and bipartite; its spokes $v_iu_i$ and short edges $v_iu_{i+1}$ form a Hamilton cycle, so it is connected.
--
--   Connectivity of $B^{(r)}_q$ gives the "connected" in Theorem 2 for $H'$; cubicity is what makes Lemma 4 applicable.
--
--   Differences from the source:
--   - encoding: cubic; bipartite → every vertex has a neighbour set of `ncard` 3; `Colorable 2`; reason: same notions
--   - encoding: the spokes and short edges form a Hamilton cycle → a Hamilton cycle `c : ZMod (2n) ≃ V(B)` whose edge set equals the set of spokes and short edges; reason: a cyclic listing of the cycle; same statement
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.8 (PDF p.10), unnumbered

import Mathlib
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_IsCyclicInterval

set_option autoImplicit false

namespace RobersonCx

/-- §4.1 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), p.8 (PDF p.10)), unnumbered: for `r ≥ 2` and `n > 2r`, `B^(r)_n` "is simple, cubic, and bipartite.
Its spokes and short edges form a Hamilton cycle, so it is connected."

**Formalization Note** Simplicity is built into `SimpleGraph`. Cubic: every vertex has exactly three neighbours;
bipartite: `Colorable 2`. "The spokes and short edges form a Hamilton cycle": a cyclic ordering
`c : ZMod (2n) ≃ V(B)` that is a Hamilton cycle (`IsHamCycle`) whose edge set is exactly the set of spokes
`v_iu_i` and short edges `v_iu_{i+1}` (`u_i = Sum.inl i`, `v_i = Sum.inr i`). -/
theorem splitB_cubic_bipartite_connected (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    (∀ v : ZMod n ⊕ ZMod n, ((splitB n r).neighborSet v).ncard = 3) ∧ (splitB n r).Colorable 2 ∧
    (∃ c : ZMod (2 * n) ≃ (ZMod n ⊕ ZMod n), IsHamCycle (splitB n r) c ∧
      cycleEdges c = {e | ∃ i : ZMod n, e = s(Sum.inr i, Sum.inl i) ∨ e = s(Sum.inr i, Sum.inl (i + 1))}) ∧
    (splitB n r).Connected := by sorry

end RobersonCx
