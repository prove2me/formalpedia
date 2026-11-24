-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral_muX
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_muX
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:56.234854+00:00
-- url     : https://prove2.me/theorems/70fdc5e6-23c2-4306-8cd7-fb49066c88c1
-- title:
--   MI: lintegral mu X
-- statement:
--   The MI construction uses the lintegral mu X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L85-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L85-L109

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_muX {x0 : Frame X.Ψ r} {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 =
      Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, GLo X x0 φ x := by sorry
