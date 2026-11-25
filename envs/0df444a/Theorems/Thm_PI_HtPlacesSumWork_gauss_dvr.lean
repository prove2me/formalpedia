-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_gauss_dvr
-- name    : PI.HtPlacesSumWork.gauss_dvr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:07:14.098549+00:00
-- url     : https://prove2.me/theorems/16b9bb2b-b528-489a-aa99-808c167ca684
-- title:
--   Ht Places Sum Work: gauss dvr
-- statement:
--   The Ht Places Sum Work construction uses the gauss dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L85-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L85-L106

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

theorem PI.HtPlacesSumWork.gauss_dvr : IsDiscreteValuationRing (Op D N la) := by sorry
