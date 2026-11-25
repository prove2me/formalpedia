-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral__C_84e056a32217
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral__C_84e056a32217
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:41.861563+00:00
-- url     : https://prove2.me/theorems/9709ca29-d484-423b-aa52-a7ea4e5e76c6
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI lintegral  C 84e056a32217: P2 M Reciprocity Theory Chart Restriction G AR Up MI lintegral  C 84e056a32217
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI lintegral  C 84e056a32217 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI lintegral  C 84e056a32217 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L35-L42

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral__C_84e056a32217 (F : (LoI X.Ψ r → ℂ) → ENNReal) :
    ∫⁻ z, F (ΦC X z) = Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, F x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«lintegral_ΦC» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral__C_84e056a32217
