-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:50.880583+00:00
-- url     : https://prove2.me/theorems/6ff61113-eb2c-40a1-91f5-ff6235fd43b7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AI I1 mk  chart Ideal X self 6bdb4b0af909: P2 M Reciprocity Theory Chart Restriction G AI I1 mk  chart Ideal X self 6bdb4b0af909
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AI I1 mk  chart Ideal X self 6bdb4b0af909 construction uses the P2 M Reciprocity Theory Chart Restriction G AI I1 mk  chart Ideal X self 6bdb4b0af909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L203-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L203-L205

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909 (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, j k⟩) = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AI».«I1».«mkₐ_chartIdeal_X_self» := P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909
