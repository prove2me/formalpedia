-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_productive_iff_prefixes_no_bottom
-- name    : TreeEquivalenceHORS.Equivalence.productive_iff_prefixes_no_bottom
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:25:01.219354+00:00
-- url     : https://prove2.me/theorems/e18bad08-e842-4a61-9cbb-43b4ab14aef6
-- title:
--   Finite prefixes detect failure of productivity
-- statement:
--   A closed ground term in a valid scheme is productive at every depth exactly when no finite prefix contains a bottom node.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem productive_iff_prefixes_no_bottom (G : HORS) (vg : G.Valid) (t : Tm)
    (ht : G.typeOf [] t = some .o) :
    (∀ d, G.ProdDepth t d) ↔ ∀ d, ∀ p ∈ G.Pref t d, p.2 ≠ .bot := by sorry

end TreeEquivalenceHORS.Equivalence
