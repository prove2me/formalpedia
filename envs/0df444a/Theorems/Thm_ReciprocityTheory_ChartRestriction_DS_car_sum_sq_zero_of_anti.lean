-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_sum_sq_zero_of_anti
-- name    : ReciprocityTheory.ChartRestriction.DS.car_sum_sq_zero_of_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:27.628892+00:00
-- url     : https://prove2.me/theorems/66ff162f-db5d-4c43-b993-65e1ad6c881b
-- title:
--   DS: car sum sq zero of anti
-- statement:
--   The DS construction uses the car sum sq zero of anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L81-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
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

theorem ReciprocityTheory.ChartRestriction.DS.car_sum_sq_zero_of_anti {R ι : Type*} [Ring R] [Module ℂ R] (s : Finset ι) (F : ι → R)
    (h : ∀ x ∈ s, ∀ y ∈ s, F x * F y = -(F y * F x)) : (∑ x ∈ s, F x) * (∑ y ∈ s, F y) = 0 := by sorry
