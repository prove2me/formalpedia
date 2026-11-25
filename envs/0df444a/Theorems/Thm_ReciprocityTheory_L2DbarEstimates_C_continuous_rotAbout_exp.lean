-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuous_rotAbout_exp
-- name    : ReciprocityTheory.L2DbarEstimates.C.continuous_rotAbout_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:09.252459+00:00
-- url     : https://prove2.me/theorems/5e07666e-ff83-4184-acd8-05aa0fd43d42
-- title:
--   C: continuous rot About exp
-- statement:
--   The C construction uses the continuous rot About exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean#L71-L73

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

theorem ReciprocityTheory.L2DbarEstimates.C.continuous_rotAbout_exp {n : ℕ} (c : V n) :
    Continuous (fun p : ℝ × V n => rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) := by sorry
