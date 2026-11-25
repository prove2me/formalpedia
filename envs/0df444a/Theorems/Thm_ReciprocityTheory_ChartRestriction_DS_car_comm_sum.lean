-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_comm_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.car_comm_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:25.719156+00:00
-- url     : https://prove2.me/theorems/2dde60d0-adca-5c0f-86da-cef8d67afba0
-- title:
--   DS: car comm sum
-- statement:
--   The DS construction uses the car comm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L63-L72

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

theorem ReciprocityTheory.ChartRestriction.DS.car_comm_sum {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ) (A : ι → R) (B : κ → R) :
    (∑ x ∈ s, A x) * (∑ y ∈ t, B y) - (∑ y ∈ t, B y) * (∑ x ∈ s, A x) =
      ∑ x ∈ s, ∑ y ∈ t, (A x * B y - B y * A x) := by sorry
