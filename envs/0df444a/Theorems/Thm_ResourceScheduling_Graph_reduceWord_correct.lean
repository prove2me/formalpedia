-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_reduceWord_correct
-- name    : ResourceScheduling.Graph.reduceWord_correct
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T06:19:37.515343+00:00
-- url     : https://prove2.me/theorems/4fbe8991-6602-4c36-8278-360dbc1f182c
-- title:
--   Correctness and quadratic size of the total graph-to-Q2 word reduction
-- statement:
--   Let $P$ be the language of graph codes admitting a partition into paths of length two, and let $Q$ be the encoded language of feasible two-machine resource-constrained schedules. Let $F$ be the total transformation that applies the non-edge resource construction to a successfully parsed graph and returns the empty word on malformed input. Then, for every word $w$,
--
--   $$w\in P\quad\Longleftrightarrow\quad F(w)\in Q,\qquad |F(w)|\le 5|w|^2+8.$$
--
--   This establishes the semantic correctness and a quadratic output-size bound for the reduction, including the empty graph and every malformed input. The graph-to-schedule equivalence is the previously proved mission theorem by mrfancypants. Polynomial-time computability in the fixed Cook Turing-machine model remains a separate obligation.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_WordReduction

namespace ResourceScheduling.Graph
theorem reduceWord_correct (w : List Letter) :
    (w ∈ pathsLang ↔ reduceWord w ∈ codeLang Q2Yes encQ2) ∧
    (reduceWord w).length ≤ 5 * w.length ^ 2 + 8 := by sorry
end ResourceScheduling.Graph
