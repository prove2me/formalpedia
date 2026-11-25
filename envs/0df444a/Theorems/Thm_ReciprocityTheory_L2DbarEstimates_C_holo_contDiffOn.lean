-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn
-- name    : ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:59.191794+00:00
-- url     : https://prove2.me/theorems/61531a10-aa46-4e6f-a230-4cb4a9c60d17
-- title:
--   C: holo cont Diff On
-- statement:
--   The C construction uses the holo cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MollifyEqConvolution.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MollifyEqConvolution.lean#L51-L54

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
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
open scoped ENNReal ContDiff Convolution

theorem ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℝ ∞ f Ω := by sorry
