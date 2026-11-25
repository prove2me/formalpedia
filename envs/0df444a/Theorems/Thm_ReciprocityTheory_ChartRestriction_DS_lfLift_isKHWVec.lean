-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfLift_isKHWVec
-- name    : ReciprocityTheory.ChartRestriction.DS.lfLift_isKHWVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:12.021798+00:00
-- url     : https://prove2.me/theorems/3d33e751-1d8e-4938-b1c2-4dfd2af5f8a5
-- title:
--   DS: lf Lift is KHWVec
-- statement:
--   The DS construction uses the lf Lift is KHWVec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L91-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L91-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem ReciprocityTheory.ChartRestriction.DS.lfLift_isKHWVec (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {μ : Fin n → ℝ}
    {x : LfIdx ε → N}
    (hw : ∀ a S, E a a (x S) + ∑ T, lfMat ε a a S T • x T = ((μ a : ℝ) : ℂ) • x S)
    (hh : ∀ a b, a < b → ε a = ε b → ∀ S, E a b (x S) + ∑ T, lfMat ε a b S T • x T = 0) :
    IsKHWVec ε (diagE ε (eT E) cpT cmT) μ (lfLift ε x) := by sorry
