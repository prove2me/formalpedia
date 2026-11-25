-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_vanS_int
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.vanS_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:10.951183+00:00
-- url     : https://prove2.me/theorems/a0527706-8f47-46d7-9cad-ecec02121012
-- title:
--   Div LA: van S int
-- statement:
--   The Div LA construction uses the van S int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L101-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L101-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.vanS_int (hn : 1 ≤ n) {a : ℕ} {G : V n → ℂ} {S : Fin n → V n → ℂ}
    (hG : G =O[𝓝 0] fun z => ‖z‖ ^ a) {c : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ z in 𝓝 0, c * ‖z‖ ^ 2 ≤ ∑ k, ‖S k z‖ ^ 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖G z‖ ^ 2 *
      (∑ k, ‖S k z‖ ^ 2) ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by sorry
