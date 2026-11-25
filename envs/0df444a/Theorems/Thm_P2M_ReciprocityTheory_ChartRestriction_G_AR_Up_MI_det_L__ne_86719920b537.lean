-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:39.170318+00:00
-- url     : https://prove2.me/theorems/ad4ab859-9754-4617-abbc-c7818b60ecbd
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  ne 86719920b537: P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  ne 86719920b537
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  ne 86719920b537 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI det L  ne 86719920b537 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L143-L146

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537 (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) : LinearMap.det (Lβ β) ≠ 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«det_Lβ_ne» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__ne_86719920b537
