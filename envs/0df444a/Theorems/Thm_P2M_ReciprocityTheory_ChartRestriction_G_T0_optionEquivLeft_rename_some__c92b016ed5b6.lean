-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:42.525627+00:00
-- url     : https://prove2.me/theorems/3a29f13c-cd8a-4a45-b5e1-75eab1eea89f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 option Equiv Left rename some  c92b016ed5b6: P2 M Reciprocity Theory Chart Restriction G T0 option Equiv Left rename some  c92b016ed5b6
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 option Equiv Left rename some  c92b016ed5b6 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 option Equiv Left rename some  c92b016ed5b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentScaledForms.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentScaledForms.lean#L162-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6 {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«optionEquivLeft_rename_some'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6
