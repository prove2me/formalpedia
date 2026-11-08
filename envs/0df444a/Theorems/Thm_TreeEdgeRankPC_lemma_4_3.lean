-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_4_3
-- name    : TreeEdgeRankPC.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:45.951187+00:00
-- url     : https://prove2.me/theorems/a52b8d38-2d9c-406a-9039-a78ff6492402
-- title:
--   Lemma 4.3 — GreedyAllocation reduces in NC¹ to Tree-Edge-Ranking, with trees of diameter at most six
-- statement:
--   Given an input $\langle K;q_1,\dots,q_d\rangle$ to GreedyAllocation as in Definition 4.2, one can construct in NC¹ a tree $T(q_1,\dots,q_d)$ such that
--   $$\mathrm{er}(T(q_1,\dots,q_d))\le K\iff \text{GreedyAllocation is feasible}.$$
--   Furthermore, $T(q_1,\dots,q_d)$ has diameter at most six.
--
--   This is the first half of the reduction behind Theorem 4.1.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - encoding: input and output as objects → the binary codes `encGA K q` and `encTree T K`; values of f on other strings are unconstrained; reason: the lemma is about inputs "as specified in Definition 4.2"
--   - encoding: diameter at most six → `∀ u v, T.dist u v ≤ 6`; reason: in a tree the longest simple path is the largest distance
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 4.3, p.15; proof, p.16

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_TreeLanguage
import Definitions.Def_TreeEdgeRankPC_GreedyAllocation
import Definitions.Def_TreeEdgeRankPC_TreeGadget

namespace TreeEdgeRankPC

/-- **Lemma 4.3**, §4.1, p.15, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Given an input ⟨K; q1, ..., qd⟩ to GreedyAllocation as specified in
Definition 4.2, one can construct in NC^1 a tree T(q1, ..., qd) such that er(T(q1, ..., qd)) ≤ K if and only if
GreedyAllocation is feasible. Furthermore, T(q1, ..., qd) has diameter at most six."

**Formalization Note.** The same function `f` works for all instances: it maps the code of a valid instance
to the code of `(T(q₁, …, q_d), K)`, numbered as in the proof on p.16. Its values on other strings are not
constrained. -/
theorem lemma_4_3 :
    ∃ f : List Bool → List Bool, NC1Computable f ∧ ∀ (K : ℕ) (q : List ℕ), GAValid K q →
      f (encGA K q) = encTree (treeOfRequirements q) K ∧
      (treeOfRequirements q).IsTree ∧
      (∀ u v, (treeOfRequirements q).dist u v ≤ 6) ∧
      (er (treeOfRequirements q) ≤ K ↔ GAFeasible K q) := by sorry

end TreeEdgeRankPC
