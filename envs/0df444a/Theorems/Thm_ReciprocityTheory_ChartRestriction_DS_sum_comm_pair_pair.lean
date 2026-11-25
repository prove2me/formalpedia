-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_comm_pair_pair
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_comm_pair_pair
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:15.510673+00:00
-- url     : https://prove2.me/theorems/6fe776d0-8a88-5f01-951f-f088f6cba114
-- title:
--   DS: sum comm pair pair
-- statement:
--   The DS construction uses the sum comm pair pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L19-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.sum_comm_pair_pair {R : Type*} [AddCommMonoid R] {ι κ ι' κ' : Type*} (s : Finset ι) (s' : Finset ι')
    (t : Finset κ) (t' : Finset κ') (f : ι → ι' → κ → κ' → R) :
    ∑ a ∈ s, ∑ b ∈ s', ∑ i ∈ t, ∑ j ∈ t', f a b i j = ∑ i ∈ t, ∑ j ∈ t', ∑ a ∈ s, ∑ b ∈ s', f a b i j := by sorry
