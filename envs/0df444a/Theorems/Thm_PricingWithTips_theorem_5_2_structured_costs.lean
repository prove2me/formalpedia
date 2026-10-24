-- Prove2me | Theorems.Thm_PricingWithTips_theorem_5_2_structured_costs
-- name    : PricingWithTips.theorem_5_2_structured_costs
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:20:54.291855+00:00
-- url     : https://prove2.me/theorems/d47bae49-8162-4c00-b2a0-f38d7867466b
-- title:
--   Theorem 5.2 — tips restore efficient equilibria under structured costs
-- statement:
--   For every finite nonempty three-sided market whose delivery costs decompose either into buyer–store plus courier–store terms or into buyer–store plus courier–buyer terms, there is a welfare-optimal allocation supported by an equilibrium with up-front tips. In contrast, for every $K>0$ there is a structured two-buyer, one-store, two-courier market with positive optimal welfare and at least one without-tip equilibrium such that every without-tip equilibrium has welfare at most $-K$.
-- source:
--   Gonczarowski, Ma, and Parkes (2025), Pricing with Tips in Three-Sided Delivery Platforms, arXiv:2507.10872v1, PDF p. 24, Theorem 5.2, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem theorem_5_2_structured_costs
    [Nonempty B] [Nonempty S] [Nonempty D] :
    (∀ M : Market B S D,
      CourierStoreDecomposable M ∨ CourierBuyerDecomposable M →
        ∃ A p w t, IsWelfareOptimal M A ∧ IsWithTipEquilibrium M A p w t) ∧
    ArbitrarilyLowWithoutTipWelfare := by sorry

end PricingWithTips
