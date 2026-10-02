-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_unary_codec_correct
-- name    : ResourceScheduling.Graph.unary_codec_correct
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T05:45:24.088572+00:00
-- url     : https://prove2.me/theorems/e385bccb-ce3a-4e9f-a355-ed112def7543
-- title:
--   Correct decoding and unique factorization of unary codes
-- statement:
--   Write $u(n)=1^n0$ for the mission's separator-terminated unary code. The parser reads a valid prefix with any suffix exactly, and every successful parse reconstructs the original word:
--
--   $$\operatorname{readUnary}(u(n)r)=(n,r),\qquad \operatorname{readUnary}(w)=(n,r)\Longrightarrow w=u(n)r.$$
--
--   Furthermore, concatenation of unary codes is injective on finite lists of natural numbers. Thus a list of fields is uniquely determined by its serialized word. The empty natural-number list and zero-valued fields are included. These facts support parsing and malformed-input handling for encoded scheduling reductions.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Codec

namespace ResourceScheduling.Graph
theorem unary_codec_correct :
    (∀ n rest, readUnary (unary n ++ rest) = some (n, rest)) ∧
    (∀ w n rest, readUnary w = some (n, rest) → w = unary n ++ rest) ∧
    Function.Injective encNatList := by sorry
end ResourceScheduling.Graph
