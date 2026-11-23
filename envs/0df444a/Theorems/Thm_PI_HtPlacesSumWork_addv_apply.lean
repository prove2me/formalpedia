-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_addv_apply
-- name    : PI.HtPlacesSumWork.addv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:00.364165+00:00
-- url     : https://prove2.me/theorems/d81581a0-cbc8-4320-ab6e-763dba2ac0b5
-- title:
--   Ht Places Sum Work: addv apply
-- statement:
--   The Ht Places Sum Work construction uses the addv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L94-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)

theorem PI.HtPlacesSumWork.addv_apply {x : L} (hx : x ≠ 0) :
    addv L v x = (((-log (v.valuation L x) : ℤ)) : WithTop ℤ) := by sorry
