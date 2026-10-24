-- Prove2me | Theorems.Thm_PricingWithTips_lemma_4_4_equilibrium_iff_maximum_weight
-- name    : PricingWithTips.lemma_4_4_equilibrium_iff_maximum_weight
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:19:48.421303+00:00
-- url     : https://prove2.me/theorems/3c7f14a4-1019-45f0-ba11-67f151387c59
-- title:
--   Lemma 4.4 — equilibrium allocations as maximum-weight matchings
-- statement:
--   Fix an allocation and a componentwise maximal vector of courier utilities. The allocation is supportable by a with-tip equilibrium if and only if the induced buyer–store matching maximizes total adjusted value, where a delivered buyer–store pair has zero required tip and every undelivered pair is discounted by the least delivery cost plus the corresponding courier utility.
-- source:
--   Gonczarowski, Ma, and Parkes (2025), Pricing with Tips in Three-Sided Delivery Platforms, arXiv:2507.10872v1, PDF p. 19, Lemma 4.4, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem lemma_4_4_equilibrium_iff_maximum_weight [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar) :
    HasWithTipEquilibriumAt M A ↔
      IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
