-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_valPl_log_le
-- name    : PI.HtPlacesSumWork.valPl_log_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:07:30.043405+00:00
-- url     : https://prove2.me/theorems/4f452c62-278b-51bb-9532-6d038b2006e8
-- title:
--   Ht Places Sum Work: val Pl log le
-- statement:
--   The Ht Places Sum Work construction uses the val Pl log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L19-L20

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

theorem PI.HtPlacesSumWork.valPl_log_le {g : ℤᵐ⁰} (hg : g ≠ 0) : g ≤ 1 ↔ log g ≤ 0 := by sorry
