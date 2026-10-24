-- Prove2me | Theorems.Thm_PricingWithTips_structured_costs_optimal_nonempty_nonfull_has_equilibrium
-- name    : PricingWithTips.structured_costs_optimal_nonempty_nonfull_has_equilibrium
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:33:42.386533+00:00
-- url     : https://prove2.me/theorems/dd1f71e3-7c2e-4fe4-b2ba-32541a030eb4
-- title:
--   Structured costs support a nonempty, non-full welfare optimum
-- statement:
--   In a finite delivery market with at least one buyer, store and courier, suppose delivery cost splits into a buyer–store term plus either a courier–store or a courier–buyer term. If an allocation maximizes welfare, contains at least one trade, and leaves at least one courier idle, then a with-tip equilibrium supports that allocation. This isolates the alternating-path argument of Theorem 5.2 from its zero-trade boundary case.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Theorem 5.2 proof, pp. 20–22 and Appendix D, pp. 35–36.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem structured_costs_optimal_nonempty_nonfull_has_equilibrium
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none) :
    HasWithTipEquilibriumAt M A := by sorry

end PricingWithTips
