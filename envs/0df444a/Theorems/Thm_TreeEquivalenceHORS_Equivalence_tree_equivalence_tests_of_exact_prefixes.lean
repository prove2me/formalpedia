-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_tree_equivalence_tests_of_exact_prefixes
-- name    : TreeEquivalenceHORS.Equivalence.tree_equivalence_tests_of_exact_prefixes
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:11:19.214182+00:00
-- url     : https://prove2.me/theorems/197bce15-4e67-4312-82f6-946c0f9cdfcd
-- title:
--   A total exact-prefix algorithm gives computable depth tests for the four equivalence languages
-- statement:
--   A total algorithm computing exact prefixes on valid closed ground terms yields a computable depth test for each of the four equivalence languages. Each input is in the language exactly when its test accepts at every depth.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages
import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem tree_equivalence_tests_of_exact_prefixes
    (pf : ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d)) :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true := by sorry

end TreeEquivalenceHORS.Equivalence
