-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_finite_environment_fixed_point
-- name    : TreeEquivalenceHORS.Equivalence.finite_environment_fixed_point
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:18:04.468324+00:00
-- url     : https://prove2.me/theorems/bb350b96-6693-46b1-bf5d-b687731da4a4
-- title:
--   The finite head-semantics iteration reaches a fixed point at the stated bound
-- statement:
--   For every valid scheme, one further simultaneous update leaves the environment computed after exactly the product of the finite type-domain cardinalities unchanged.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem finite_environment_fixed_point (G : HORS) (v : G.Valid) : G.Phi G.etaStar = G.etaStar := by sorry

end TreeEquivalenceHORS.Equivalence
