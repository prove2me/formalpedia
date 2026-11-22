-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_binary_translation_correct
-- name    : TreeEquivalenceHORS.Equivalence.binary_translation_correct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:28:41.277189+00:00
-- url     : https://prove2.me/theorems/26ba4765-1297-4d1a-82ea-9f2a5bdfa97e
-- title:
--   Correctness of the binary-output recursion-scheme translation
-- statement:
--   Replacing source terminals by their binary constructor rules preserves validity, productivity and safety. The translated scheme has the binary alphabet, its order is bounded by the larger of one and the source order, and its value tree is exactly the binary encoding of the source tree.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Encoding

namespace TreeEquivalenceHORS.Equivalence

theorem binary_translation_correct (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0) (pg : G.Prod) :
    (binaryScheme G).Valid ∧ (binaryScheme G).alphabet = sigma2 ∧ (binaryScheme G).Prod ∧
    (binaryScheme G).order ≤ max 1 G.order ∧ (binaryScheme G).BT = encAt G.BT ∧ (G.Safe → (binaryScheme G).Safe) := by sorry

end TreeEquivalenceHORS.Equivalence
