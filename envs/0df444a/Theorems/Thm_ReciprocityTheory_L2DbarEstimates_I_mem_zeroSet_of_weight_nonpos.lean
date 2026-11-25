-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_mem_zeroSet_of_weight_nonpos
-- name    : ReciprocityTheory.L2DbarEstimates.I.mem_zeroSet_of_weight_nonpos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:21.975563+00:00
-- url     : https://prove2.me/theorems/d7301504-0b54-4344-b381-93a4a6be59c1
-- title:
--   I: mem zero Set of weight nonpos
-- statement:
--   The I construction uses the mem zero Set of weight nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L13-L25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
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
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.mem_zeroSet_of_weight_nonpos {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hr : r ≠ 0) (x : M) (h : ev n g ph r x ≤ 0) : x ∈ zeroSet n g := by sorry
