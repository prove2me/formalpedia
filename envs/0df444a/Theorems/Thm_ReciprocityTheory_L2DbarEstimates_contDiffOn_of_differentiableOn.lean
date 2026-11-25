-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn
-- name    : ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:58.732913+00:00
-- url     : https://prove2.me/theorems/641e0f2a-be04-4700-8f25-f16e5d5b4fb4
-- title:
--   L2 Dbar Estimates: cont Diff On of differentiable On
-- statement:
--   The L2 Dbar Estimates construction uses the cont Diff On of differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/HoloSmooth.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/HoloSmooth.lean#L11-L12

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffAtComplex
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (n : ℕ) (g : V n → ℂ) (U : Set (V n)) (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℂ ∞ g U := by sorry
