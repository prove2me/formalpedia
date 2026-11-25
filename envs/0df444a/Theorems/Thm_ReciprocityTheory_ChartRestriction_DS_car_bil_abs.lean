-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_bil_abs
-- name    : ReciprocityTheory.ChartRestriction.DS.car_bil_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:56.334479+00:00
-- url     : https://prove2.me/theorems/3d2a5884-fcd7-40b4-a5dc-a07c3edaf949
-- title:
--   DS: car bil abs
-- statement:
--   The DS construction uses the car bil abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L38-L54

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

theorem ReciprocityTheory.ChartRestriction.DS.car_bil_abs {R : Type*} [Ring R] (p1 m1 p2 m2 δ δ' : R) (h1 : m1 * p2 + p2 * m1 = δ)
    (h2 : m2 * p1 + p1 * m2 = δ') (hp : p1 * p2 + p2 * p1 = 0) (hm : m1 * m2 + m2 * m1 = 0) :
    p1 * m1 * (p2 * m2) - p2 * m2 * (p1 * m1) = p1 * δ * m2 - p2 * δ' * m1 := by sorry
