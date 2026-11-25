-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral_cpt_muX_indep_of_isOrtho
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_cpt_muX_indep_of_isOrtho
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:06.174083+00:00
-- url     : https://prove2.me/theorems/eeda3610-3a20-4c1f-a0b4-6a1e5ee74d7f
-- title:
--   MI: lintegral cpt mu X indep of is Ortho
-- statement:
--   The MI construction uses the lintegral cpt mu X indep of is Ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfL.lean#L111-L120

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_cpt_muX_indep_of_isOrtho {x0 x0' : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (hx0' : X.IsOrtho x0') {φ : Frame X.Ψ r → ENNReal}
    (hφm : Measurable φ) (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muX X x0' := by sorry
