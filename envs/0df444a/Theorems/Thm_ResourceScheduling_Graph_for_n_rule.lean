-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_for_n_rule
-- name    : ResourceScheduling.Graph.for_n_rule
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:58:40.788018+00:00
-- url     : https://prove2.me/theorems/5b6f09d8-b125-40c2-8b49-345b98b2c65b
-- title:
--   for n rule
-- statement:
--   The explicit range-loop macro enumerates the indices from zero through dimension minus one, preserves the numeric bound, and establishes an indexed invariant at the endpoint.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg

namespace ResourceScheduling.Graph
theorem for_n_rule (counter idx : GraphReg) (hc : n ≠ counter) (hi : idx ≠ n)
    (hic : idx ≠ counter) (p : GraphProgram.Code)
    (hw : p.writes n = false ∧ p.writes idx = false ∧ p.writes counter = false)
    (B N : ℕ) (P : ℕ → RAMState GraphReg → Prop)
    (hpc : ∀ k x a, P k (x.set counter a) ↔ P k x)
    (hpi : ∀ k x a, P k (x.set idx a) ↔ P k x)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hn : s.val n = N) (hp : P 0 s)
    (hstep : ∀ k < N, ∀ x, RAMBound B x → x.val n = N → x.val idx = k → P k x →
      RAMSafe p B x ∧ P (k + 1) (p.eval x)) :
    RAMSafe (GraphProgram.forN counter idx hc p) B s ∧
      ((GraphProgram.forN counter idx hc p).eval s).val idx = N ∧
      ((GraphProgram.forN counter idx hc p).eval s).val counter = 0 ∧
      P N ((GraphProgram.forN counter idx hc p).eval s) := by sorry
end ResourceScheduling.Graph
