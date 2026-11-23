-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_gauss_lift
-- name    : PI.HtPlacesSumWork.gauss_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:12.349079+00:00
-- url     : https://prove2.me/theorems/21d84e7d-5d7c-47f1-b131-e790f39c2225
-- title:
--   Ht Places Sum Work: gauss lift
-- statement:
--   The Ht Places Sum Work construction uses the gauss lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L108-L111

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

theorem PI.HtPlacesSumWork.gauss_lift (x : OT K D N) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) x) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N x) := by sorry
