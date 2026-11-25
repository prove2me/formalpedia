-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_real_smul_smul
-- name    : ReciprocityTheory.L2DbarEstimates.C.real_smul_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:05.604427+00:00
-- url     : https://prove2.me/theorems/c6e66d20-0f79-43e4-a117-16f265397c1e
-- title:
--   C: real smul smul
-- statement:
--   The C construction uses the real smul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L105-L106

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

theorem ReciprocityTheory.L2DbarEstimates.C.real_smul_smul (t : ℝ) (μ : ℂ) (e : V n) : t • (μ • e) = ((t : ℂ) * μ) • e := by sorry
