-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_finite_semantic_domains
-- name    : TreeEquivalenceHORS.Equivalence.finite_semantic_domains
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T19:15:20.833653+00:00
-- url     : https://prove2.me/theorems/246d8ac9-cfa5-4c54-b781-be98dea53a05
-- title:
--   Least table values and monotone application in the finite semantics
-- statement:
--   Every finite semantic domain contains its specified least value. Application of a valid function table to a valid argument gives an element of the result domain, and this operation is monotone jointly in the table and the argument.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem finite_semantic_domains :
    (∀ σ : Ty, botV σ ∈ enum σ ∧ (∀ x ∈ enum σ, leT σ (botV σ) x = true)) ∧
    (∀ (σ τ : Ty) (f x : SVal), f ∈ enum (.arr σ τ) → x ∈ enum σ → appT σ f x ∈ enum τ) ∧
    ∀ (σ τ : Ty) (f g x y : SVal), f ∈ enum (.arr σ τ) → g ∈ enum (.arr σ τ) →
      x ∈ enum σ → y ∈ enum σ → leT (.arr σ τ) f g = true → leT σ x y = true →
      leT τ (appT σ f x) (appT σ g y) = true := by sorry

end TreeEquivalenceHORS.Equivalence
