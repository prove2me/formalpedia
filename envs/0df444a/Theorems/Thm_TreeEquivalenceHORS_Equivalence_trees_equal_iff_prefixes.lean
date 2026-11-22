-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_trees_equal_iff_prefixes
-- name    : TreeEquivalenceHORS.Equivalence.trees_equal_iff_prefixes
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:25:01.161557+00:00
-- url     : https://prove2.me/theorems/3d1556fe-5283-472f-a30e-dc6229515b45
-- title:
--   Finite prefixes characterize equality of two value trees
-- statement:
--   Two closed ground terms in valid schemes with the same ranked alphabet generate identical value trees if and only if all their finite prefixes agree.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem trees_equal_iff_prefixes (G H : HORS) (vg : G.Valid) (vh : H.Valid)
    (alph : G.alphabet = H.alphabet) (t u : Tm)
    (ht : G.typeOf [] t = some .o) (hu : H.typeOf [] u = some .o) :
    G.BTat t = H.BTat u ↔ ∀ d, G.Pref t d = H.Pref u d := by sorry

end TreeEquivalenceHORS.Equivalence
