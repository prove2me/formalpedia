-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_binary_encoding_reflects_tree_equality
-- name    : TreeEquivalenceHORS.Equivalence.binary_encoding_reflects_tree_equality
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:22:23.430179+00:00
-- url     : https://prove2.me/theorems/04c0af7f-51f5-4c1b-8859-34291e1e583c
-- title:
--   The binary tree encoding reflects equality of productive value trees
-- statement:
--   For two valid productive schemes over the intermediate ranked alphabet, equality of their binary encodings is equivalent to equality of their original value trees.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Encoding

namespace TreeEquivalenceHORS.Equivalence

theorem binary_encoding_reflects_tree_equality (G H : HORS) (vg : G.Valid) (vh : H.Valid)
    (ag : G.alphabet = sigma0) (ah : H.alphabet = sigma0) (pg : G.Prod) (ph : H.Prod) :
    encAt G.BT = encAt H.BT ↔ G.BT = H.BT := by sorry

end TreeEquivalenceHORS.Equivalence
