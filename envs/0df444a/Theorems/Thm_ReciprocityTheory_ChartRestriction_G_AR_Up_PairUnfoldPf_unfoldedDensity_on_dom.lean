-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_unfoldedDensity_on_dom
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.unfoldedDensity_on_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:37.828319+00:00
-- url     : https://prove2.me/theorems/207d5a82-45ed-4ced-bfeb-f455f82991d4
-- title:
--   Pair Unfold Pf: unfolded Density on dom
-- statement:
--   The Pair Unfold Pf construction uses the unfolded Density on dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPf.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPf.lean#L39-L41

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.unfoldedDensity_on_dom {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by sorry
