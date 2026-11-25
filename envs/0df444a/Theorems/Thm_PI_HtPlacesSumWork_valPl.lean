-- Prove2me | Theorems.Thm_PI_HtPlacesSumWork_valPl
-- name    : PI.HtPlacesSumWork.valPl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:07:19.465561+00:00
-- url     : https://prove2.me/theorems/f1221db0-4a6b-52f7-b321-6a82aa6a9778
-- title:
--   Ht Places Sum Work: val Pl
-- statement:
--   The Ht Places Sum Work construction uses the val Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L476-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean#L476-L503

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
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

theorem PI.HtPlacesSumWork.valPl {ϖ : O} (hϖ : Irreducible ϖ) (e : AddValuation L (WithTop ℤ) → ℤ)
    (he : ∀ w ∈ PlacesOver O L, (e w : WithTop ℤ) = w (algebraMap O L ϖ)) :
    (PlacesOver O L).Finite ∧
      ∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L), (fres F L w : ℤ) * e w =
        Module.finrank F L := by sorry
