-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_tail_tendsto
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.tail_tendsto
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:31.520035+00:00
-- url     : https://prove2.me/theorems/86ff3585-436c-401f-b3b5-d87732d2945d
-- title:
--   FPw: tail tendsto
-- statement:
--   The FPw construction uses the tail tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/ExpNEllMem.lean#L100-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/ExpNEllMem.lean#L100-L170

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.tail_tendsto {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    (∀ N, Integrable (fun v => gN N (ellL q a v) * Pf q a F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ))) ∧
    Tendsto (fun N => paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G) atTop (𝓝 0) := by sorry
