-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurePreserving_rotAbout
-- name    : ReciprocityTheory.L2DbarEstimates.C.measurePreserving_rotAbout
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:09.813828+00:00
-- url     : https://prove2.me/theorems/f8bedd5f-f1c9-4df7-a45d-66c914040976
-- title:
--   C: measure Preserving rot About
-- statement:
--   The C construction uses the measure Preserving rot About property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L18-L21

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

theorem ReciprocityTheory.L2DbarEstimates.C.measurePreserving_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (rotAbout c a) volume volume := by sorry
