-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral_comp_LA
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_comp_LA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:11.472723+00:00
-- url     : https://prove2.me/theorems/1a581e79-c49c-4d4b-b0d2-5fea3ebdd14f
-- title:
--   MI: lintegral comp LA
-- statement:
--   The MI construction uses the lintegral comp LA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfG.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfG.lean#L54-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfG
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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_comp_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ τ, (A τ).det ≠ 0)
    {F : (Ix ι r → ℂ) → ENNReal} (hF : Measurable F) :
    ∫⁻ v, F (LA A v) = ENNReal.ofReal (Complex.normSq (∏ τ, (A τ).det ^ r))⁻¹ * ∫⁻ v, F v := by sorry
