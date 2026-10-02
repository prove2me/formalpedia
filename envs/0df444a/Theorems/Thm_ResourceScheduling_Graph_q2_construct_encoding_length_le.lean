-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_q2_construct_encoding_length_le
-- name    : ResourceScheduling.Graph.q2_construct_encoding_length_le
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T05:28:01.978401+00:00
-- url     : https://prove2.me/theorems/ad078628-61de-4bdf-b337-23a9b542d1fa
-- title:
--   A quadratic size bound for the unary graph-to-Q2 encoding
-- statement:
--   Let $d$ be a graph on $3t$ vertices, encoded as unary $t$ followed by its adjacency matrix, and let $L$ be the length of this graph code. Apply the mission\'s non-edge resource construction, use speeds $2$ and $1$, and threshold $t$. The exact unary code of the resulting scheduling instance satisfies
--
--   $$|\operatorname{encQ2}((2,1),\operatorname{reduce}(d))|\le 5L^2+8.$$
--
--   The bound includes $t=0$ and uses the existing encodings without modification. It supplies an output-size estimate for the subsequent Turing-machine implementation; a running-time bound is a separate obligation.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph
theorem q2_construct_encoding_length_le (d : GraphData) :
    (encQ2 (![2, 1], reduce d)).length ≤ 5 * (encGraph d).length ^ 2 + 8 := by sorry
end ResourceScheduling.Graph
