-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:38.348913+00:00
-- url     : https://prove2.me/theorems/13efe1af-703a-40e5-87ff-7822cba5457c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI jac U L  09c946809e4d: P2 M Reciprocity Theory Chart Restriction G AR Up MI jac U L  09c946809e4d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI jac U L  09c946809e4d construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI jac U L  09c946809e4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L35-L42

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ) :
    jacU (Lβ β y) = jacβ β * jacU y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«jacU_Lβ» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
