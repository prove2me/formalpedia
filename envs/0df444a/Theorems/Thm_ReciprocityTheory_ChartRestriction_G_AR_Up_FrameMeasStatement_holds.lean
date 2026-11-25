-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FrameMeasStatement_holds
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FrameMeasStatement_holds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:45.896286+00:00
-- url     : https://prove2.me/theorems/b67ff060-85de-4802-80c0-40f4b744f8dc
-- title:
--   Up: Frame Meas Statement holds
-- statement:
--   The Up construction uses the Frame Meas Statement holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPf.lean#L16-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPf.lean#L16-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up.MI ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable FM.haarF FM.haarIx
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FrameMeasStatement_holds : FrameMeasStatement (E := E) := by sorry
