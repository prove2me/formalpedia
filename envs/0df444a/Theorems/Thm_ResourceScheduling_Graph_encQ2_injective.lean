-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_encQ2_injective
-- name    : ResourceScheduling.Graph.encQ2_injective
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T05:50:44.294932+00:00
-- url     : https://prove2.me/theorems/eb82dc77-a50f-417b-9e74-22f7f7ad867a
-- title:
--   Uniqueness of the original Q2 scheduling encoding
-- statement:
--   The separator-terminated unary encoding of the two-machine scheduling instances is injective. For any two pairs of positive integer speeds and resource-constrained instance data $p$ and $q$,
--
--   $$\operatorname{encQ2}(p)=\operatorname{encQ2}(q)\Longrightarrow p=q.$$
--
--   In particular, an encoded word uniquely determines both speeds, the numbers of jobs and resources, every requirement, and the makespan threshold. The statement includes zero jobs and zero resources, and is needed when interpreting encoded yes-instances in the language reduction.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_ResDot11

namespace ResourceScheduling.Graph
theorem encQ2_injective : Function.Injective encQ2 := by sorry
end ResourceScheduling.Graph
