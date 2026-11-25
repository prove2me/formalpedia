-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_grad_log_sq
-- name    : ReciprocityTheory.L2DbarEstimates.C.grad_log_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:54.362452+00:00
-- url     : https://prove2.me/theorems/bb28fb74-f2d0-569f-9381-a3580788a44a
-- title:
--   C: grad log sq
-- statement:
--   The C construction uses the grad log sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCut.lean#L26-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCut.lean#L26-L53

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.grad_log_sq {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (h0 : F z ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2 ≤
      4 * (∑ j, ‖fderiv ℂ F z (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2) / ‖F z‖ ^ 2 := by sorry
