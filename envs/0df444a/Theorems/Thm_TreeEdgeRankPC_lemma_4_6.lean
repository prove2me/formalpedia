-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_6
-- name    : TreeEdgeRankPC.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:45.860073+00:00
-- url     : https://prove2.me/theorems/25874a3f-49f9-43ff-bb65-cc75fd006c7f
-- title:
--   Lemma 4.6 — AM2CVP reduces in NC¹ to GreedyAllocation via $\mathcal G(C)$, with $K=18m$
-- statement:
--   Given an $m$-node instance $C$ of AM2CVP, one can construct in NC¹ the instance $\mathcal G(C)=\langle K;q_1,\dots,q_d\rangle$ of GreedyAllocation, and it is feasible if and only if $c_m=1$. The construction has $d=O(m)$ positive requirements of $O(m)$ bits each, and $K=18m$.
--
--   This is the second half of the reduction behind Theorem 4.1: it encodes monotone circuit evaluation into the run of the greedy procedure.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - reading: d = O(m) requirements of O(m) bits → ∃ absolute c chosen before C with d ≤ c·m and every qᵢ < 2^{c·m}; reason: the standard meaning of the asymptotics, with the constant independent of C
--   - encoding: input and output as objects → the binary codes `C.enc` and `encGA (18m) GC`; values of f on other strings are unconstrained; reason: the lemma is about AM2CVP instances
--   - encoding: G(C) as a multiset → the list `GC`, in node order; reason: the same requirements with multiplicities
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.6, p.16; eq. (4.5), p.20

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_GreedyAllocation
import Definitions.Def_TreeEdgeRankPC_AM2CVP
import Definitions.Def_TreeEdgeRankPC_Gadgets

namespace TreeEdgeRankPC

/-- **Lemma 4.6**, §4.2, p.16 (with the instance `G(C)` of eq. (4.5), p.20), arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Given an m-node instance C of
AM2CVP, one can construct in NC^1 an instance G(C) = ⟨K; q1, ..., qd⟩ of GreedyAllocation that is feasible if and
only if cm = 1. The construction has d = O(m) positive requirements of O(m) bits each and K = 18m."

**Formalization Note.** `c` is an absolute constant, chosen before `C`: `d ≤ c·m`, and each requirement is below
`2^{c·m}`, i.e. has at most `c·m` bits. The same `f` works for all instances, and its values on non-codes are
not constrained. `GAValid` says the requirements are positive and the instance is one of Definition 4.2. -/
theorem lemma_4_6 :
    ∃ (f : List Bool → List Bool) (c : ℕ), NC1Computable f ∧ ∀ C : AM2Instance,
      f C.enc = encGA (18 * C.nodes.length) C.GC ∧
      GAValid (18 * C.nodes.length) C.GC ∧
      C.GC.length ≤ c * C.nodes.length ∧
      (∀ a ∈ C.GC, a < 2 ^ (c * C.nodes.length)) ∧
      (GAFeasible (18 * C.nodes.length) C.GC ↔ C.value = true) := by sorry

end TreeEdgeRankPC
