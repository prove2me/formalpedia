-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_positive_finite_denotation_converges
-- name    : TreeEquivalenceHORS.Equivalence.positive_finite_denotation_converges
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:21:21.209495+00:00
-- url     : https://prove2.me/theorems/6613d597-33c6-47d6-b930-98b85bbbbbcf
-- title:
--   Positive finite denotation implies head convergence
-- statement:
--   In every valid scheme, a positive finite-model value for a closed ground term yields a finite head evaluation to a terminal.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem positive_finite_denotation_converges (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : G.den [] G.etaStar [] t = .bit true) : ∃ c us, G.HeadConv t c us := by sorry

end TreeEquivalenceHORS.Equivalence
