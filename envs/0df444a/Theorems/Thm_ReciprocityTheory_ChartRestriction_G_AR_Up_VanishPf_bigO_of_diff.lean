-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_VanishPf_bigO_of_diff
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.bigO_of_diff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:38.726792+00:00
-- url     : https://prove2.me/theorems/9ce94d8d-0e3a-5917-95a8-98f0a2509a05
-- title:
--   Vanish Pf: big O of diff
-- statement:
--   The Vanish Pf construction uses the big O of diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L12-L16

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.bigO_of_diff {n : ℕ} {f : V n → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖f z‖ ≤ C * ‖z‖ := by sorry
