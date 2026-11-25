-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoD_ext_glue
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.ext_glue
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:23.295508+00:00
-- url     : https://prove2.me/theorems/7af72859-fd99-531d-8d80-a93e8455988a
-- title:
--   Onto D: ext glue
-- statement:
--   The Onto D construction uses the ext glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L53-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L53-L92

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set Metric
noncomputable section
variable {n : ℕ} {Ω : Set (V n)} {g : V n → ℂ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.ext_glue (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) {F' : V n → ℂ} (hF' : DifferentiableOn ℂ F' {z | z ∈ Ω ∧ g z ≠ 0})
    (hL2 : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧
      ∫⁻ y in ball z ρ \ {y | g y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, g z ≠ 0 → F z = F' z := by sorry
