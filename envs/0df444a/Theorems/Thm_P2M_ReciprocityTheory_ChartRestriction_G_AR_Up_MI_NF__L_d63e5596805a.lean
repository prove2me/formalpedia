-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_NF__L_d63e5596805a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_NF__L_d63e5596805a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:05.773015+00:00
-- url     : https://prove2.me/theorems/833a4f2a-dea1-5fa9-86fc-be8636c5755a
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI NF  L d63e5596805a: P2 M Reciprocity Theory Chart Restriction G AR Up MI NF  L d63e5596805a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI NF  L d63e5596805a construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI NF  L d63e5596805a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L25-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_NF__L_d63e5596805a (z : V (nd X)) : NF X (ΦL X z) = nmat X z := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«NF_ΦL» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_NF__L_d63e5596805a
