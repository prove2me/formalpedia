-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_expand
-- name    : ReciprocityTheory.ChartRestriction.DS.carKinv_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:17.921184+00:00
-- url     : https://prove2.me/theorems/621fa80f-ee83-4ad8-a02a-c6fb9007bf30
-- title:
--   DS: car Kinv expand
-- statement:
--   The DS construction uses the car Kinv expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L27-L34

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

theorem ReciprocityTheory.ChartRestriction.DS.carKinv_expand {R : Type*} [Ring R] (P Q A S : R) (hQA : Q * A = A * Q)
    (hPS : P * S = S * P) :
    P * Q * (A + S) - (A + S) * (P * Q) = (P * A - A * P) * Q - P * (S * Q - Q * S) := by sorry
