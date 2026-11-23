-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__76e6fa524bc5
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__76e6fa524bc5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:42.360094+00:00
-- url     : https://prove2.me/theorems/18818250-90fc-4232-8765-a923538dac23
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  76e6fa524bc5: P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  76e6fa524bc5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  76e6fa524bc5 construction uses the P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  76e6fa524bc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L10-L13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__76e6fa524bc5 {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = 0)
    (h2 : B * C + C * B = δ) : A * B * C - C * (A * B) = A * δ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«carKinv_triple₁» := P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__76e6fa524bc5
