-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_smoothR_sumSq
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_smoothR_sumSq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:25.388092+00:00
-- url     : https://prove2.me/theorems/d546a758-ea80-41ab-8dfa-60b9b8377154
-- title:
--   I: evl smooth R sum Sq
-- statement:
--   The I construction uses the evl smooth R sum Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L102-L105

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_smoothR_sumSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) :
    SmoothR n z (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) := by sorry
