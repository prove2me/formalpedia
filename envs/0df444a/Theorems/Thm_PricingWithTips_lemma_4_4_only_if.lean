-- Prove2me | Theorems.Thm_PricingWithTips_lemma_4_4_only_if
-- name    : PricingWithTips.lemma_4_4_only_if
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:26:48.891753+00:00
-- url     : https://prove2.me/theorems/446fcd02-f4da-42d3-a11f-71d2ed79e94f
-- title:
--   Equilibrium implies maximum adjusted buyer matching
-- statement:
--   For a finite delivery market and maximal courier-utility vector, if a with-tip equilibrium supports an allocation, then the allocation’s induced buyer–store matching maximizes the total adjusted buyer value. This is the only-if direction of Lemma 4.4.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Lemma 4.4, Appendix C, pp. 33–34.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem lemma_4_4_only_if [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (heq : HasWithTipEquilibriumAt M A) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by sorry

end PricingWithTips
