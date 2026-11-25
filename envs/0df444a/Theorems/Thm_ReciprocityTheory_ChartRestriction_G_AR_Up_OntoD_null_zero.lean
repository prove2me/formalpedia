-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoD_null_zero
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.null_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:10.760775+00:00
-- url     : https://prove2.me/theorems/5c2ed162-3a73-4d21-982a-c0c58a4346b7
-- title:
--   Onto D: null zero
-- statement:
--   The Onto D construction uses the null zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfD.lean#L39-L51

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD.null_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : volume (Ω ∩ {z | g z = 0}) = 0 := by sorry
