-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_5
-- name    : TreeEdgeRankPC.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:13.470166+00:00
-- url     : https://prove2.me/theorems/2bedd606-5189-4fc6-89a4-2e98e6d2e941
-- title:
--   Lemma 4.5 — $\mathrm{wt}(\mathrm{crit}(B_q))=q$
-- statement:
--   For any positive integer $q$, the branch gadget $B_q$ satisfies
--   $$\mathrm{wt}(\mathrm{crit}(B_q))=q.$$
--
--   Every requirement of a GreedyAllocation instance is therefore the critical weight of an explicit branch whose vertices lie within distance three of its root.
--
--   Differences from the source:
--   - encoding: the vertices of B_q → the numbers 0, 1, … of the proof on p.16, with the root r numbered 0; reason: any numbering gives the same tree
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.5, p.15; gadget B_q, p.15

import Mathlib
import Definitions.Def_TreeEdgeRankPC_CriticalSet
import Definitions.Def_TreeEdgeRankPC_TreeGadget

namespace TreeEdgeRankPC

/-- **Lemma 4.5**, §4.1, p.15, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "For any positive integer q, wt(crit(Bq)) = q."

**Formalization Note.** `gadget q` is the printed `B_q`, with root `r` numbered `0`. -/
theorem lemma_4_5 (q : ℕ) (hq : 1 ≤ q) : wt (crit (gadget q) 0) = q := by sorry

end TreeEdgeRankPC
