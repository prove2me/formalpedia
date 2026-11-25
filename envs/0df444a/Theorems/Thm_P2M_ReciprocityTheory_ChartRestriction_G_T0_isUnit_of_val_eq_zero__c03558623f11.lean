-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:16:56.851906+00:00
-- url     : https://prove2.me/theorems/ef16bb04-aa6e-5c5a-849c-d7b9ad6504e9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 is Unit of val eq zero  c03558623f11: P2 M Reciprocity Theory Chart Restriction G T0 is Unit of val eq zero  c03558623f11
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 is Unit of val eq zero  c03558623f11 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 is Unit of val eq zero  c03558623f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L204-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L204-L212

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11 {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hz : v z = 0) : IsUnit (⟨z, h⟩ : vRing v) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«isUnit_of_val_eq_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11
