-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:27.124614+00:00
-- url     : https://prove2.me/theorems/a1fceb4b-4ebb-408d-9f83-60f5648b9dde
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AI I1 chart Swap mk  4f83fe97b485: P2 M Reciprocity Theory Chart Restriction G AI I1 chart Swap mk  4f83fe97b485
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AI I1 chart Swap mk  4f83fe97b485 construction uses the P2 M Reciprocity Theory Chart Restriction G AI I1 chart Swap mk  4f83fe97b485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L314-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L314-L319

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485 {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩))) (p : Σ k, ι k) :
    chartSwap hV i j hu (Ideal.Quotient.mkₐ F (chartIdeal V i) (X p)) =
      ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AI».«I1».«chartSwap_mkₐ» := P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485
