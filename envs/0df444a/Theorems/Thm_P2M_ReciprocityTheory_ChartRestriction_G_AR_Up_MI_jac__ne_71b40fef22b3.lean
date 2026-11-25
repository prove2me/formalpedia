-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:41.690924+00:00
-- url     : https://prove2.me/theorems/b0484c53-d831-5646-bb71-707e7ef1994f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI jac  ne 71b40fef22b3: P2 M Reciprocity Theory Chart Restriction G AR Up MI jac  ne 71b40fef22b3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI jac  ne 71b40fef22b3 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI jac  ne 71b40fef22b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean#L148-L153

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3 (β : ι → Matrix (Fin r) (Fin r) ℂ) (hd : ∀ τ b, β τ b b ≠ 0) : jacβ β ≠ 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«jacβ_ne» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3
