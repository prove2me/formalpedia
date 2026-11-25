-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasLineDerivAt_lineFirstVariation
-- name    : ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_lineFirstVariation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:12.605491+00:00
-- url     : https://prove2.me/theorems/5a8e08dd-0ef7-54f2-81a9-7fa80eb0c7a3
-- title:
--   C: has Line Deriv At line First Variation
-- statement:
--   The C construction uses the has Line Deriv At line First Variation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L51-L71

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

theorem ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_lineFirstVariation {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
      (lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) z (μ • e) := by sorry
