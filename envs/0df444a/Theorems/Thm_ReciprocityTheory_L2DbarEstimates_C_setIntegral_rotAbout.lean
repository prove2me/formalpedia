-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_setIntegral_rotAbout
-- name    : ReciprocityTheory.L2DbarEstimates.C.setIntegral_rotAbout
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:19.746234+00:00
-- url     : https://prove2.me/theorems/2248f451-cee8-47a6-944f-f022a056c397
-- title:
--   C: set Integral rot About
-- statement:
--   The C construction uses the set Integral rot About property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L51-L56

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

theorem ReciprocityTheory.L2DbarEstimates.C.setIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V n → E) :
    ∫ z in ball c R, g (rotAbout c a z) = ∫ z in ball c R, g z := by sorry
