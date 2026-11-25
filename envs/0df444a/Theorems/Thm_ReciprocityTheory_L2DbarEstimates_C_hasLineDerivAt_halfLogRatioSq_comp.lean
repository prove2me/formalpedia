-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasLineDerivAt_halfLogRatioSq_comp
-- name    : ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_halfLogRatioSq_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:48.006883+00:00
-- url     : https://prove2.me/theorems/4e830bcd-09dd-498a-8d41-dabb999a2ecc
-- title:
--   C: has Line Deriv At half Log Ratio Sq comp
-- statement:
--   The C construction uses the has Line Deriv At half Log Ratio Sq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L33-L49

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
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
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_halfLogRatioSq_comp {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => cutP ε (‖F w‖ ^ 2)) (lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) z
      (μ • e) := by sorry
