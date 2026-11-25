-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_comp
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartSwap_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:40.826427+00:00
-- url     : https://prove2.me/theorems/930ef7f0-670b-4a8b-a97d-65fede39514a
-- title:
--   I1: chart Swap comp
-- statement:
--   The I1 construction uses the chart Swap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L321-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L321-L335

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartSwap_comp {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩)))
    (hv : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V i) (X ⟨k, j k⟩))) :
    (chartSwap hV j i hv).comp (chartSwap hV i j hu) = AlgHom.id F _ := by sorry
