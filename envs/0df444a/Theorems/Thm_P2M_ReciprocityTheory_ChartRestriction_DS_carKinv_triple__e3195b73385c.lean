-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:47.069703+00:00
-- url     : https://prove2.me/theorems/0a50199f-171e-4b29-80dc-6f155fbb46e5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  e3195b73385c: P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  e3195b73385c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  e3195b73385c construction uses the P2 M Reciprocity Theory Chart Restriction DS car Kinv triple  e3195b73385c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L15-L18

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = δ)
    (h2 : B * C + C * B = 0) : A * B * C - C * (A * B) = -(δ * B) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«carKinv_triple₂» := P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c
