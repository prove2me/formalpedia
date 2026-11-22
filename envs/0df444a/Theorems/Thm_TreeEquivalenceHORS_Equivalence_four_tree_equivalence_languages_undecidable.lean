-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_four_tree_equivalence_languages_undecidable
-- name    : TreeEquivalenceHORS.Equivalence.four_tree_equivalence_languages_undecidable
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:06:02.337365+00:00
-- url     : https://prove2.me/theorems/28f87c54-5134-4ed9-a071-97527e2bd730
-- title:
--   Tree equivalence is undecidable for all four scheme languages
-- statement:
--   Each of the four tree-equivalence languages is undecidable and every co-c.e. predicate many-one reduces to it. The same computable map works for all four, and produces safe, productive order-at-most-four pairs over the fixed binary alphabet.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages

namespace TreeEquivalenceHORS.Equivalence

theorem four_tree_equivalence_languages_undecidable :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      (∀ A : ℕ → Prop, CoCE A → A ≤₀ P) ∧ ¬ ComputablePred P := by sorry

end TreeEquivalenceHORS.Equivalence
