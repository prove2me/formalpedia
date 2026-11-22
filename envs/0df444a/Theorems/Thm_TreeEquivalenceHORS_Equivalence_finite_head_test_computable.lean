-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_finite_head_test_computable
-- name    : TreeEquivalenceHORS.Equivalence.finite_head_test_computable
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:35:35.76669+00:00
-- url     : https://prove2.me/theorems/ec8e2926-62a7-469d-ae21-a5058b5d870d
-- title:
--   A total numerical algorithm computes the finite-semantics head test
-- statement:
--   There is a total computable Boolean function on pairs of numerical scheme and term codes. On every valid scheme and closed ground term it returns true exactly when the specified final finite denotation is the positive bit.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem finite_head_test_computable :
    ∃ b : ℕ × ℕ → Bool, Computable b ∧ ∀ (G : HORS) (t : Tm), G.Valid → G.typeOf [] t = some .o →
      (b (Encodable.encode G, Encodable.encode t) = true ↔ G.den [] G.etaStar [] t = .bit true) := by sorry

end TreeEquivalenceHORS.Equivalence
