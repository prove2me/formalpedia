-- Prove2me | Theorems.Thm_TreeEdgeRankPC_theorem_4_1
-- name    : TreeEdgeRankPC.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:26.285064+00:00
-- url     : https://prove2.me/theorems/e2a2e6d1-515b-4780-a84d-1e2e5760c12e
-- title:
--   Theorem 4.1 — NC¹ many-one reduction from AM2CVP to Tree-Edge-Ranking on trees of diameter at most six
-- statement:
--   There exists an NC¹ many-one reduction from AM2CVP to Tree-Edge-Ranking for trees of diameter at most six. That is, there is an NC¹-computable $f$ such that $f(x)$ is always the code of a tree of diameter at most six with a bound $K$, and
--   $$x\in\mathrm{AM2CVP}\iff f(x)\in\text{Tree-Edge-Ranking}.$$
--
--   Together with the P-hardness of AM2CVP, this gives the hardness half of Theorem 1.1.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - encoding: a many-one reduction on instances → a function on all strings; a string that encodes no AM2CVP instance goes to a fixed no-instance; reason: p.20: "The source restrictions can also be checked in NC¹"; non-encodings are not in AM2CVP
--   - reading: "to Tree-Edge-Ranking for trees of diameter at most six" → every output is a code of such a tree, and the equivalence holds for both the general and the diameter-six language; reason: the two languages agree on such outputs; both are used by Theorem 1.1
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Theorem 4.1, p.14; p.20 (source restrictions; proof)

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_TreeLanguage
import Definitions.Def_TreeEdgeRankPC_AM2CVP

namespace TreeEdgeRankPC

/-- **Theorem 4.1**, §4, p.14, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "There exists an NC^1 many-one reduction from AM2CVP to Tree-Edge-Ranking for
trees of diameter at most six."

**Formalization Note.** The reduction's every output is the code of a tree of diameter at most six with a bound
`K`: strings that do not encode an AM2CVP instance go to a fixed no-instance (p.20: "The source restrictions can
also be checked in NC¹"). The equivalence is stated for both the general and the restricted language. -/
theorem theorem_4_1 :
    ∃ f : List Bool → List Bool, NC1Computable f ∧ ∀ x,
      (∃ (n : ℕ) (T : SimpleGraph (Fin n)) (K : ℕ),
        T.IsTree ∧ (∀ u v, T.dist u v ≤ 6) ∧ f x = encTree T K) ∧
      (x ∈ AM2CVP ↔ f x ∈ TER) ∧ (x ∈ AM2CVP ↔ f x ∈ TER6) := by sorry

end TreeEdgeRankPC
