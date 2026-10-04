-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_reduceWord_polyTime
-- name    : ResourceScheduling.Graph.reduceWord_polyTime
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T06:52:43.891593+00:00
-- url     : https://prove2.me/theorems/0a6f9f42-2c1d-4f23-bc5e-dd18f743b73d
-- title:
--   Cook-machine polynomial time for the concrete graph-to-Q2 word transformation
-- statement:
--   Let $F$ be the published total graph-to-scheduling transformation: successfully parsed graph codes are sent to the original non-edge resource construction with speeds $2,1$, and malformed words are sent to the empty word. The remaining computational obligation is that $F$ is computable by a Cook one-tape deterministic transducer in polynomial time. Precisely, there exist a finite work alphabet, injective input and output alphabet maps, one fixed machine $M$, and one exponent $k$ such that for every word $w$,
--
--   $$T_M(w)\le |w|^k+k,\qquad \operatorname{output}_M(w)=F(w).$$
--
--   The output equality uses the specified alphabet maps and the original convention of reading from the final head position and trimming trailing blanks. Semantic correctness and the quadratic output-size bound have been proved separately; this node isolates the outstanding machine construction and running-time proof.
-- source:
--   The exact remaining computational obligation for the ResourceScheduling.Graph scheduling mission, using the published WordReduction definition and the original CookPvsNP_defs machine model. It is a concrete implementation obligation for the graph-to-scheduling construction of Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), Theorem 3; the paper does not state this particular Lean implementation. This node is intentionally Open, not a claimed completed result.

import Definitions.Def_ResourceScheduling_Graph_WordReduction

namespace ResourceScheduling.Graph
theorem reduceWord_polyTime : CookPvsNP.PolyTimeComputable reduceWord := by sorry
end ResourceScheduling.Graph
