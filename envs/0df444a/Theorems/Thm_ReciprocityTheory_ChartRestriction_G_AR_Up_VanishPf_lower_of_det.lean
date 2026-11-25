-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_VanishPf_lower_of_det
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:02.048166+00:00
-- url     : https://prove2.me/theorems/6d42726b-a63a-55fa-b4a7-d32bb1d6a483
-- title:
--   Vanish Pf: lower of det
-- statement:
--   The Vanish Pf construction uses the lower of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L18-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L18-L51

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det {n : ℕ} (hn : 0 < n) {σ : V n → V n} (h0 : σ 0 = 0)
    (hdet : (fderiv ℂ σ 0).det ≠ 0) : ∃ c > 0, ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ≤ ‖σ z‖ := by sorry
