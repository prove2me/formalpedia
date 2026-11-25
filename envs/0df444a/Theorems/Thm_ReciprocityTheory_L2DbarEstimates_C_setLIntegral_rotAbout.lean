-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_setLIntegral_rotAbout
-- name    : ReciprocityTheory.L2DbarEstimates.C.setLIntegral_rotAbout
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:01.222273+00:00
-- url     : https://prove2.me/theorems/078f02d2-fce8-42c4-ae0b-74bbf31c31bd
-- title:
--   C: set LIntegral rot About
-- statement:
--   The C construction uses the set LIntegral rot About property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L44-L49

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
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

theorem ReciprocityTheory.L2DbarEstimates.C.setLIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    (g : V n → ℝ≥0∞) :
    ∫⁻ z in ball c R, g (rotAbout c a z) = ∫⁻ z in ball c R, g z := by sorry
