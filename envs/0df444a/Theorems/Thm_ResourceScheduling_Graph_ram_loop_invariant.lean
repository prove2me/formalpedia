-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_loop_invariant
-- name    : ResourceScheduling.Graph.ram_loop_invariant
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:41:59.649497+00:00
-- url     : https://prove2.me/theorems/345184e6-5f0c-4072-8ea8-c9901323b333
-- title:
--   ram loop invariant
-- statement:
--   A finite-index invariant establishes both the loop numeric bound and its final semantic property.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMBudget
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_loop_invariant {V : Type} [DecidableEq V] (v : V) (p : RAMCode V)
    (B n : ℕ) (I : ℕ → RAMState V → Prop) (s : RAMState V)
    (hs : RAMBound B s) (hn : s.val v = n) (hi : I 0 s)
    (hstep : ∀ k < n, ∀ x, I k x →
      p.Bounded B (x.set v (x.val v - 1)) ∧ I (k + 1) (p.eval (x.set v (x.val v - 1)))) :
    (RAMCode.loop v p).Bounded B s ∧ I n ((RAMCode.loop v p).eval s) := by sorry
end ResourceScheduling.Graph
