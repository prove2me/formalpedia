-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKHWVec_sub
-- name    : ReciprocityTheory.ChartRestriction.DS.isKHWVec_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:03.264489+00:00
-- url     : https://prove2.me/theorems/a18c3b18-6c8f-5f40-8157-122e0d5ccf80
-- title:
--   DS: is KHWVec sub
-- statement:
--   The DS construction uses the is KHWVec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L31-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth
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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.isKHWVec_sub {μ : Fin n → ℝ} {v w : M} (hv : IsKHWVec ε E μ v)
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (v - w) := by sorry
