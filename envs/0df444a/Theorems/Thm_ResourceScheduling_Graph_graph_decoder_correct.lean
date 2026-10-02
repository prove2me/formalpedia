-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_graph_decoder_correct
-- name    : ResourceScheduling.Graph.graph_decoder_correct
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T06:05:21.069111+00:00
-- url     : https://prove2.me/theorems/759d4e65-f4bd-4114-8e97-22474809eadb
-- title:
--   Exact parsing and reconstruction of graph codes
-- statement:
--   Let $E$ be the original encoding of a graph on $3t$ vertices by unary $t$ followed by its row-major adjacency matrix, and let $D$ be the total graph parser. Then
--
--   $$D(E(G))=\operatorname{some}(G),\qquad D(w)=\operatorname{some}(G)\Longrightarrow E(G)=w.$$
--
--   Thus every encoded graph is reconstructed exactly, and every successful parse certifies the entire input word. This covers the empty graph and excludes extra trailing symbols, malformed sizes, loops, and asymmetric matrices. These facts prepare the reduction on arbitrary words; they do not assert a Turing-machine running-time bound.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Decoder

namespace ResourceScheduling.Graph
theorem graph_decoder_correct :
    (∀ d, decodeGraph (encGraph d) = some d) ∧
    (∀ w d, decodeGraph w = some d → encGraph d = w) := by sorry
end ResourceScheduling.Graph
