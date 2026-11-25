-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integrableOn_rotAbout_iff
-- name    : ReciprocityTheory.L2DbarEstimates.C.integrableOn_rotAbout_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:34.117902+00:00
-- url     : https://prove2.me/theorems/d4ba2bc4-a0db-44f1-92e3-aa5c16a0c4b8
-- title:
--   C: integrable On rot About iff
-- statement:
--   The C construction uses the integrable On rot About iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L58-L66

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

theorem ReciprocityTheory.L2DbarEstimates.C.integrableOn_rotAbout_iff {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] (g : V n → E) :
    IntegrableOn (fun z => g (rotAbout c a z)) (ball c R) ↔ IntegrableOn g (ball c R) := by sorry
