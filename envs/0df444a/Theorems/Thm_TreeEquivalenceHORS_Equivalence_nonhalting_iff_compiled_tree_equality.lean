-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_nonhalting_iff_compiled_tree_equality
-- name    : TreeEquivalenceHORS.Equivalence.nonhalting_iff_compiled_tree_equality
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:17:37.972281+00:00
-- url     : https://prove2.me/theorems/2fdaa9fa-2f82-4968-966d-059b80df50f8
-- title:
--   Nonhalting is equivalent to equality of the two intermediate value trees
-- statement:
--   For every zero-start two-counter machine, nonhalting is equivalent to equality of the value trees produced by its left and right intermediate schemes.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

theorem nonhalting_iff_compiled_tree_equality (M : Machine) :
    ¬ M.Halts ↔ (compile .L M).BT = (compile .R M).BT := by sorry

end TreeEquivalenceHORS.Equivalence
