-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_one_mode
-- name    : ReciprocityTheory.ChartRestriction.DS.car_one_mode
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:44.624909+00:00
-- url     : https://prove2.me/theorems/2509834d-13d6-4781-9d99-2288c29d7c20
-- title:
--   DS: car one mode
-- statement:
--   The DS construction uses the car one mode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L50-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
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

theorem ReciprocityTheory.ChartRestriction.DS.car_one_mode :
    IsCAR (fun _ _ : Fin 1 => cpOne) (fun _ _ : Fin 1 => cmOne) ∧
      ∀ x y : EuclideanSpace ℂ (Fin 2), inner ℂ (cpOne x) y = inner ℂ x (cmOne y) := by sorry
