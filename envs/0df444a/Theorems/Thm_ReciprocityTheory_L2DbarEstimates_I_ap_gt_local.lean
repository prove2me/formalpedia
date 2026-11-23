-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_local
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_gt_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:52.193807+00:00
-- url     : https://prove2.me/theorems/0690a8b5-fa14-4606-b95a-62aeee31ed80
-- title:
--   I: ap gt local
-- statement:
--   The I construction uses the ap gt local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L14-L36

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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_gt_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (hS : (zeroSet n g).Finite)
    (hW : IsLocalData n g ph r W m) (x : M) (hx : ev n g ph r x < m) :
    gt n z g c W =ᶠ[𝓝 x]
      fun y => (∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y := by sorry
