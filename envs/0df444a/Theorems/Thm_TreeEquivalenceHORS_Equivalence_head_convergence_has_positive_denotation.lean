-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_head_convergence_has_positive_denotation
-- name    : TreeEquivalenceHORS.Equivalence.head_convergence_has_positive_denotation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:23:41.6739+00:00
-- url     : https://prove2.me/theorems/822ae796-3350-4abc-a9f0-578127f1fbb7
-- title:
--   Finite head convergence implies positive denotation
-- statement:
--   In every valid scheme, a closed ground term which head-converges has positive denotation at the specified finite environment.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem head_convergence_has_positive_denotation (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : ∃ c us, G.HeadConv t c us) : G.den [] G.etaStar [] t = .bit true := by sorry

end TreeEquivalenceHORS.Equivalence
