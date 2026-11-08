-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_8
-- name    : TreeEdgeRankPC.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:54.032844+00:00
-- url     : https://prove2.me/theorems/2bc638af-e5c5-4bba-888f-9a5d7ae6bb03
-- title:
--   Lemma 4.8 — GreedyAllocation is feasible iff the greedy procedure never rejects
-- statement:
--   A GreedyAllocation instance $\langle K;q_1,\dots,q_d\rangle$ (with $K\ge1$, $d\ge1$ and positive requirements) is feasible if and only if the corresponding greedy procedure, processing the clocks $K-1,\dots,0$, never rejects.
--
--   Feasibility of an instance is thus reduced to the run of a deterministic clock-by-clock procedure, which the circuit simulation then controls.
--
--   Differences from the source:
--   - encoding: a run with ties broken arbitrarily → a function of the multiset of residuals; reason: covering any of several equal residuals leaves the same multiset
--   - encoding: the partition X_1, …, X_d of [K] → a map `σ : Fin K → Fin d`, with 0-based ranks and weight 2^x; reason: the same partitions; positive requirements force nonempty parts
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.8, p.17; Definition 4.2, p.14; Definition 4.7, p.17

import Mathlib
import Definitions.Def_TreeEdgeRankPC_GreedyAllocation

namespace TreeEdgeRankPC

/-- **Lemma 4.8**, §4.2, p.17 (with Definitions 4.2, p.14, and 4.7, p.17), arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "A GreedyAllocation instance
is feasible if and only if the corresponding greedy procedure never rejects."

**Formalization Note.** An instance has `K ≥ 1`, `d ≥ 1` and positive requirements, as in Definition 4.2. All
of these are needed: for `K = 0` with a requirement, or `d = 0` with `K ≥ 1`, the procedure does not reject
while no partition exists. "Never rejects" is `(greedyRun K q).isSome`. -/
theorem lemma_4_8 (K : ℕ) (q : List ℕ) (h : GAValid K q) :
    GAFeasible K q ↔ (greedyRun K q).isSome = true := by sorry

end TreeEdgeRankPC
