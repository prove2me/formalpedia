-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:40.473009+00:00
-- url     : https://prove2.me/theorems/cdac06a7-d166-4971-99ef-17d442cdc747
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI to Matrix L  zero ad1479de9b67: P2 M Reciprocity Theory Chart Restriction G AR Up MI to Matrix L  zero ad1479de9b67
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI to Matrix L  zero ad1479de9b67 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI to Matrix L  zero ad1479de9b67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfD.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfD.lean#L73-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67 (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«toMatrix_Lβ_zero» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67
