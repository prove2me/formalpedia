-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_realLine_fderiv
-- name    : ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_realLine_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:27.482935+00:00
-- url     : https://prove2.me/theorems/a81fc29a-c15a-4964-9657-25019b0331e4
-- title:
--   C: has Deriv At real Line fderiv
-- statement:
--   The C construction uses the has Deriv At real Line fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L126-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L126-L146

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
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

theorem ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_realLine_fderiv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℂ F (z + t • (μ • e)) e) (complexLineSecondDeriv F z e * μ) 0 := by sorry
