-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sum_univ_pm
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_sum_univ_pm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:12.834803+00:00
-- url     : https://prove2.me/theorems/dc5bdfd2-1439-4b23-8a6c-34a478060a29
-- title:
--   DS: csq sum univ pm
-- statement:
--   The DS construction uses the csq sum univ pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L10-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.csq_sum_univ_pm {R : Type*} [AddCommMonoid R] (ε : Fin n → Bool) (f : Fin n → R) :
    ∑ a, f a = ∑ a ∈ plusIdx ε, f a + ∑ a ∈ minusIdx ε, f a := by sorry
