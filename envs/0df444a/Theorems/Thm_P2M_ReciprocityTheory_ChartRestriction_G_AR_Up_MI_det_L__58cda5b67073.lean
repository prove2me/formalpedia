-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__58cda5b67073
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__58cda5b67073
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:38.957938+00:00
-- url     : https://prove2.me/theorems/ac52ae28-0c1e-4c82-a389-1f26426bb44c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  58cda5b67073: P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  58cda5b67073
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  58cda5b67073 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  58cda5b67073 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfD.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfD.lean#L93-L101

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__58cda5b67073 (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«det_Lβ» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__58cda5b67073
