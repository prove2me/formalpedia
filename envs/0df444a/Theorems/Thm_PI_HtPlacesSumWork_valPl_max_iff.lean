-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_valPl_max_iff
-- name    : PI.HtPlacesSumWork.valPl_max_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:19.310793+00:00
-- url     : https://prove2.me/theorems/f81d42b2-e054-4b1a-92a8-625aee1d3688
-- title:
--   Ht Places Sum Work: val Pl max iff
-- statement:
--   The Ht Places Sum Work construction uses the val Pl max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L29-L51

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

theorem PI.HtPlacesSumWork.valPl_max_iff {Φ : Type*} [Field Φ] (V : ValuationSubring Φ)
    (u : AddValuation Φ (WithTop ℤ)) (hV : ∀ x, x ∈ V ↔ 0 ≤ u x) (y : V) :
    y ∈ maximalIdeal V ↔ 0 < u (y : Φ) := by sorry
