-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_support
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_cutExt_support
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:25.841455+00:00
-- url     : https://prove2.me/theorems/e56bf677-da87-5cd5-9218-ff582afd1253
-- title:
--   I: ap cut Ext support
-- statement:
--   The I construction uses the ap cut Ext support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L128-L136

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical

theorem ReciprocityTheory.L2DbarEstimates.I.ap_cutExt_support {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (x : M) (hx : x ∉ ⋃ p ∈ hS.toFinset, closure (W p)) :
    cutExt n z g ph r c W χ ε x = 0 := by sorry
