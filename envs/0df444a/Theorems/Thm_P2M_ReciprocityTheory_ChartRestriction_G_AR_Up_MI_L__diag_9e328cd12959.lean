-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:12.982407+00:00
-- url     : https://prove2.me/theorems/4dd7d00c-dc5b-481f-b096-b24efbb39e90
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI L  diag 9e328cd12959: P2 M Reciprocity Theory Chart Restriction G AR Up MI L  diag 9e328cd12959
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI L  diag 9e328cd12959 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI L  diag 9e328cd12959 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L23-L33

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959 (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ)
    (τ : ι) (b : Fin r) : Lβ β y (dI τ b) = β τ b b * y (dI τ b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«Lβ_diag» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959
