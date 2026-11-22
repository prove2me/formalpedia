-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_syntax_and_code_tests
-- name    : TreeEquivalenceHORS.Equivalence.syntax_and_code_tests
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:08:25.458183+00:00
-- url     : https://prove2.me/theorems/7e25e628-3f47-4110-8d4f-71ce55c34b2a
-- title:
--   Computable syntactic restrictions on encoded pairs of recursion schemes
-- statement:
--   A total numerical test decides pair validity, the fixed binary alphabet and order bound when requested, and safety when requested. There is a computable numerical projection to the start term, and every successfully decoded pair re-encodes to its input code.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages

namespace TreeEquivalenceHORS.Equivalence

theorem syntax_and_code_tests :
    (∃ q : ℕ → ℕ → Bool, Computable₂ q ∧ ∀ k n, q k n = true ↔
      ∃ G H : HORS, Encodable.decode n = some (G,H) ∧ ValidPair G H ∧
        (0 < k → G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ H.order ≤ 4) ∧
        (k = 3 → G.Safe ∧ H.Safe)) ∧
    (∃ start : ℕ → ℕ, Computable start ∧ ∀ G : HORS,
      start (Encodable.encode G) = Encodable.encode (Tm.nt G.start)) ∧
    (∀ n (G H : HORS), Encodable.decode n = some (G,H) → Encodable.encode (G,H) = n) := by sorry

end TreeEquivalenceHORS.Equivalence
