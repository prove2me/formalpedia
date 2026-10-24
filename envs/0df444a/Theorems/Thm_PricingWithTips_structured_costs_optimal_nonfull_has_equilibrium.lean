-- Prove2me | Theorems.Thm_PricingWithTips_structured_costs_optimal_nonfull_has_equilibrium
-- name    : PricingWithTips.structured_costs_optimal_nonfull_has_equilibrium
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:28:45.98738+00:00
-- url     : https://prove2.me/theorems/1932ec06-16e0-4d91-a4df-b4af6025ab51
-- title:
--   Structured costs support a non-full welfare optimum
-- statement:
--   In a finite delivery market with at least one buyer, store, and courier, assume courier costs decompose into a buyer–store term plus either a courier–store term or a courier–buyer term. If a feasible allocation maximizes total welfare and at least one courier is idle, then that same allocation is supported by a with-tip equilibrium. This is the non-full case of the constructive support argument for Theorem 5.2.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Theorem 5.2 proof, pp. 20–22 and Appendix D, pp. 35–36

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

/-- The remaining non-full case of the positive direction of Theorem 5.2. -/
theorem structured_costs_optimal_nonfull_has_equilibrium
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    HasWithTipEquilibriumAt M A := by sorry

end PricingWithTips
