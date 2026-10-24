-- Prove2me | Theorems.Thm_PricingWithTips_lemma_4_4_if
-- name    : PricingWithTips.lemma_4_4_if
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:26:47.505076+00:00
-- url     : https://prove2.me/theorems/549d477c-3794-4249-9d74-b6f8d0748b93
-- title:
--   Maximum adjusted buyer matching admits an equilibrium
-- statement:
--   For a finite delivery market and maximal courier-utility vector, if the allocation’s induced buyer–store matching maximizes total adjusted buyer value, then the allocation is supported by a with-tip equilibrium. This is the if direction of Lemma 4.4.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Lemma 4.4, Appendix C, pp. 33–34.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem lemma_4_4_if [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (hmax : IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar)) :
    HasWithTipEquilibriumAt M A := by sorry

end PricingWithTips
