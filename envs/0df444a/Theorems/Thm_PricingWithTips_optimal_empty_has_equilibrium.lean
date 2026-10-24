-- Prove2me | Theorems.Thm_PricingWithTips_optimal_empty_has_equilibrium
-- name    : PricingWithTips.optimal_empty_has_equilibrium
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:33:41.819836+00:00
-- url     : https://prove2.me/theorems/539181d5-7ab0-4310-ab92-fc0f411e0169
-- title:
--   An empty welfare optimum admits a with-tip equilibrium
-- statement:
--   In a finite delivery market with at least one courier, if the empty allocation maximizes welfare, it is supported by a with-tip equilibrium. Any individual trade would have nonpositive welfare, so zero prices, wages and tips suffice: the minimum tip for an order is at least its courier cost, hence at least the buyer’s value.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Theorem 5.2 proof, pp. 20–22 (zero-trade boundary case).

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem optimal_empty_has_equilibrium [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hempty : ∀ b, A.assigned b = none)
    (hoptimal : IsWelfareOptimal M A) :
    HasWithTipEquilibriumAt M A := by sorry

end PricingWithTips
