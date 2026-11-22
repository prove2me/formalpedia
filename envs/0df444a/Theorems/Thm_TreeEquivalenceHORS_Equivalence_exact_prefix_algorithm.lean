-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_exact_prefix_algorithm
-- name    : TreeEquivalenceHORS.Equivalence.exact_prefix_algorithm
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:42:18.627348+00:00
-- url     : https://prove2.me/theorems/1cfa46da-f122-4390-adeb-0a4fcd015154
-- title:
--   Total computability of the exact finite prefix on encoded inputs
-- statement:
--   There is a total computable function on a scheme code, a term code, and a depth, returning the encoded exact prefix whenever the scheme is valid and the term is closed and ground.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem exact_prefix_algorithm :
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := by sorry

end TreeEquivalenceHORS.Equivalence
