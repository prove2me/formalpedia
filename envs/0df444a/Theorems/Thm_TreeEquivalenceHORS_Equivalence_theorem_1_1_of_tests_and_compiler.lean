-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_theorem_1_1_of_tests_and_compiler
-- name    : TreeEquivalenceHORS.Equivalence.theorem_1_1_of_tests_and_compiler
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:16:16.898603+00:00
-- url     : https://prove2.me/theorems/e6a38ff0-2d88-4dcf-b821-94a66242eced
-- title:
--   Classification of the four tree-equivalence languages from depth tests and a uniform reduction
-- statement:
--   Computable tests at every depth and one computable reduction of universal nonhalting into valid, binary, order-four, safe, productive pairs suffice for co-c.e.-completeness and undecidability of all four equivalence languages.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages

namespace TreeEquivalenceHORS.Equivalence

theorem theorem_1_1_of_tests_and_compiler
    (tests : ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true)
    (F : ℕ → HORS × HORS) (hF : Computable (fun n => Encodable.encode (F n)))
    (good : ∀ n, ∀ G ∈ [(F n).1, (F n).2],
      G.Valid ∧ G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ G.Prod ∧ G.Safe)
    (correct : ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔ (F n).1.BT = (F n).2.BT) :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := by sorry

end TreeEquivalenceHORS.Equivalence
