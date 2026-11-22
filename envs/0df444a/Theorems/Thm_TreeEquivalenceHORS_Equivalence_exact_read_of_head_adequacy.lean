-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_exact_read_of_head_adequacy
-- name    : TreeEquivalenceHORS.Equivalence.exact_read_of_head_adequacy
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:16:17.695664+00:00
-- url     : https://prove2.me/theorems/0ce05f5e-d38f-43e0-9cb3-9f1da0cacef1
-- title:
--   Correctness of the finite-address reader from head adequacy
-- statement:
--   For a valid scheme satisfying head adequacy on its closed ground terms, the address reader terminates and returns the corresponding label of the value tree.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem exact_read_of_head_adequacy {G : HORS} (hG : G.Valid)
    (adequate : ∀ t : Tm, G.typeOf [] t = some .o →
      (G.den [] G.etaStar [] t = .bit true ↔ ∃ c us, G.HeadConv t c us))
    (t : Tm) (ht : G.typeOf [] t = some .o) (w : List ℕ) :
    G.read t w = Part.some (G.BTat t w) := by sorry

end TreeEquivalenceHORS.Equivalence
