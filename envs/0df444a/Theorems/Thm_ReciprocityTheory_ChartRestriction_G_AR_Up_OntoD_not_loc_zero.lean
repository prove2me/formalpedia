-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoD_not_loc_zero
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.not_loc_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:22.932678+00:00
-- url     : https://prove2.me/theorems/0617d9f3-8d6b-447c-9ca9-3645f9459939
-- title:
--   Onto D: not loc zero
-- statement:
--   The Onto D construction uses the not loc zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L12-L37

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.not_loc_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : ∀ z ∈ Ω, ¬ g =ᶠ[𝓝 z] 0 := by sorry
