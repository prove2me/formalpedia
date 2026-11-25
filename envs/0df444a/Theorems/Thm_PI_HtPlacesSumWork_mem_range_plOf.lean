-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_mem_range_plOf
-- name    : PI.HtPlacesSumWork.mem_range_plOf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:07:40.145682+00:00
-- url     : https://prove2.me/theorems/d5326c15-1169-44d1-83e1-2cd8922ad19e
-- title:
--   Ht Places Sum Work: mem range pl Of
-- statement:
--   The Ht Places Sum Work construction uses the mem range pl Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L327-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L327-L349

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
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]

theorem PI.HtPlacesSumWork.mem_range_plOf {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ Q, plOf O L Q = w := by sorry
