-- Prove2me | Theorems.Thm_TreeEdgeRankPC_theorem_1_1
-- name    : TreeEdgeRankPC.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:11.932035+00:00
-- url     : https://prove2.me/theorems/987bdcec-d0a4-4a2c-8626-e6c52e9fdca3
-- title:
--   Theorem 1.1 — deciding $\mathrm{er}(T)\le K$ is P-complete under NC¹ many-one reductions, already for trees of diameter at most six
-- statement:
--   Given a tree $T$ and an integer $K\ge0$, deciding whether $T$ has edge ranking at most $K$ is P-complete under NC¹ many-one reductions, already for trees of diameter at most six. Explicitly, each of the two languages
--
--   1. Tree-Edge-Ranking, for all trees, and
--   2. Tree-Edge-Ranking, for trees of diameter at most six,
--
--   belongs to P, and every language in P reduces to it by a logspace-uniform NC¹ many-one reduction.
--
--   This settles the parallel complexity of tree edge ranking: Problem B.1.2 of Greenlaw, Hoover and Ruzzo, *Limits to Parallel Computation*.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - reading: "P-complete ..., already for trees of diameter at most six" → two claims, for all trees and for diameter at most six, each with membership and hardness; reason: the sentence asserts the problem and its restriction are both P-complete
--   - encoding: the instance (T, K) and problems in P → binary code `encTree T K`, languages over {0, 1}, P = the published `CookPvsNP.P Bool`; reason: the standard setting of [GHR95]; the code is injective and a non-code is no instance
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_TreeLanguage

namespace TreeEdgeRankPC

/-- **Theorem 1.1**, §1, p.2, Giliberti–Hajiaghayi–Yun, *Parallel Edge Ranking of Trees*, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Given a tree T and an
integer K ≥ 0, deciding whether T has edge ranking at most K is P-complete under NC^1 many-one reductions, already
for trees of diameter at most six."

**Formalization Note.** Two claims, each with both halves of P-completeness (membership in `CookPvsNP.P Bool`, and
a logspace-uniform NC¹ many-one reduction from every language in it): for all trees, and for trees of diameter at
most six. `K` is in binary. -/
theorem theorem_1_1 : PCompleteNC1 TER ∧ PCompleteNC1 TER6 := by sorry

end TreeEdgeRankPC
