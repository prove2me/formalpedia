-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_eq_sum
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_gt_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:01.274862+00:00
-- url     : https://prove2.me/theorems/1a7c6803-bc04-42f9-ac26-4d73599e2555
-- title:
--   I: ap gt eq sum
-- statement:
--   The I construction uses the ap gt eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L8-L12

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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_gt_eq_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (y : M) :
    gt n z g c W y = ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y := by sorry
