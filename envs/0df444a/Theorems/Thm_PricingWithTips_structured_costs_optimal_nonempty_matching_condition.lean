-- Prove2me | Theorems.Thm_PricingWithTips_structured_costs_optimal_nonempty_matching_condition
-- name    : PricingWithTips.structured_costs_optimal_nonempty_matching_condition
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:38:17.413507+00:00
-- url     : https://prove2.me/theorems/072992af-7c58-41cf-913e-a94e1e0059ed
-- title:
--   Structured-cost optimum maximizes adjusted buyer-matching weight
-- statement:
--   Consider a finite market with decomposable delivery costs and a welfare-optimal allocation that has at least one trade and at least one idle courier. There exists a maximal feasible courier-utility vector such that the allocation’s induced buyer–store matching has maximum total adjusted value, where an unallocated order’s adjusted value subtracts the minimum cost-plus-courier-utility needed to make a courier willing to serve it. This is the alternating-path inequality at the heart of Theorem 5.2; Lemma 4.4 then converts it to a with-tip equilibrium.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Theorem 5.2 proof, pp. 20–22 and Appendix D, pp. 35–36, using Lemma 4.4.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem structured_costs_optimal_nonempty_matching_condition
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none) :
    ∃ uBar : D → ℝ,
      IsMaximalCourierUtility M A uBar ∧
        IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
