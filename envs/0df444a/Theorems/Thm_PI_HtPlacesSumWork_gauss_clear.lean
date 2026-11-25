-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_gauss_clear
-- name    : PI.HtPlacesSumWork.gauss_clear
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:00.694248+00:00
-- url     : https://prove2.me/theorems/f2ee2eb4-4d01-4961-8d31-922ea56a7db7
-- title:
--   Ht Places Sum Work: gauss clear
-- statement:
--   The Ht Places Sum Work construction uses the gauss clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L113-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

theorem PI.HtPlacesSumWork.gauss_clear (p : KTp K D N) :
    ∃ x : OT K D N, ∃ n : 𝓞 K, n ≠ 0 ∧
      OTtoKT K D N x = OTtoKT K D N (MvPolynomial.C n) * p := by sorry
