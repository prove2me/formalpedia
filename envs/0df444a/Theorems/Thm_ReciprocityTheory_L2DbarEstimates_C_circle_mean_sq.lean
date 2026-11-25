-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_circle_mean_sq
-- name    : ReciprocityTheory.L2DbarEstimates.C.circle_mean_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:42.947918+00:00
-- url     : https://prove2.me/theorems/704920a0-a25d-5181-a981-4e8d69bed2c7
-- title:
--   C: circle mean sq
-- statement:
--   The C construction uses the circle mean sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/Circle.lean#L64-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/Circle.lean#L64-L126

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
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
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.C.circle_mean_sq {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖u (c + Complex.exp ((θ : ℂ) * I) • w)‖ₑ ^ 2 := by sorry
