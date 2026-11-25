-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_ineq_pt
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ineq_pt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:40.536899+00:00
-- url     : https://prove2.me/theorems/00fcd9e6-5f2f-5f1a-826e-36cad695b478
-- title:
--   Pair Unfold Pf: ineq pt
-- statement:
--   The Pair Unfold Pf construction uses the ineq pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPf.lean#L94-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPf.lean#L94-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ineq_pt (a b : ℂ) (w : ℝ≥0∞) {k : ℝ} (hk : 0 < k) :
    ‖a * (starRingEnd ℂ) b * ((w.toReal : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖a‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖b‖ ^ 2) * w) := by sorry
