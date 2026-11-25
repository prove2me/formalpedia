-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_VanishPf_crit_div
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:24.690696+00:00
-- url     : https://prove2.me/theorems/297e107f-aae6-563b-b99a-4cc7b0e56154
-- title:
--   Vanish Pf: crit div
-- statement:
--   The Vanish Pf construction uses the crit div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L53-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L53-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_VanishAtSStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  Filter Asymptotics
open scoped ENNReal
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ⊤ := by sorry
