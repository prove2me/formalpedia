-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_gauss_C_mem_iff
-- name    : PI.HtPlacesSumWork.gauss_C_mem_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:53.502986+00:00
-- url     : https://prove2.me/theorems/cb61d6db-737b-5ba1-86f6-3ee992979348
-- title:
--   Ht Places Sum Work: gauss C mem iff
-- statement:
--   The Ht Places Sum Work construction uses the gauss C mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/GaussMaximalIdeal.lean#L10-L19

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

theorem PI.HtPlacesSumWork.gauss_C_mem_iff (s : 𝓞 K) :
    (MvPolynomial.C s : OT K D N) ∈ laT D N la ↔ s ∈ la.asIdeal := by sorry
