-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont__0_55f500e1d2be
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont__0_55f500e1d2be
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:26.188438+00:00
-- url     : https://prove2.me/theorems/5bbca892-d5ce-4839-9f58-0ae134c6c0a7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up FM cont  0 55f500e1d2be: P2 M Reciprocity Theory Chart Restriction G AR Up FM cont  0 55f500e1d2be
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up FM cont  0 55f500e1d2be construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up FM cont  0 55f500e1d2be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L74-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont__0_55f500e1d2be (τ : X.Ψ) : Continuous fun y : X.dom => β0 X y.1 τ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FM».«cont_β0» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont__0_55f500e1d2be
