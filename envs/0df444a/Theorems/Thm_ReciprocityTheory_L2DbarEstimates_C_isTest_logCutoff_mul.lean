-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_isTest_logCutoff_mul
-- name    : ReciprocityTheory.L2DbarEstimates.C.isTest_logCutoff_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:40.595908+00:00
-- url     : https://prove2.me/theorems/14f8bce8-3775-4d32-9901-db07c9a1528d
-- title:
--   C: is Test log Cutoff mul
-- statement:
--   The C construction uses the is Test log Cutoff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L107-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L107-L133

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
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
open scoped ENNReal ContDiff
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.isTest_logCutoff_mul {Ω : Set (V n)} {F : V n → ℂ}
    (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z) {k : ℝ} (hk : 0 < k) {g : V n → ℂ} (hg : IsTest Ω g) :
    IsTest (Ω \ {z | F z = 0}) (fun z => (extCut F k z : ℂ) * g z) := by sorry
