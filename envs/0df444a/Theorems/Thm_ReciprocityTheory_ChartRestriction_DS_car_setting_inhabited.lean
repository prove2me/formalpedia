-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_setting_inhabited
-- name    : ReciprocityTheory.ChartRestriction.DS.car_setting_inhabited
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:54.788768+00:00
-- url     : https://prove2.me/theorems/3fad849f-0b09-4a07-8559-6ba1504398b6
-- title:
--   DS: car setting inhabited
-- statement:
--   The DS construction uses the car setting inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L39-L44

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

theorem ReciprocityTheory.ChartRestriction.DS.car_setting_inhabited :
    IsGlRep (0 : Fin n → Fin n → Module.End ℂ (Fock n)) ∧ IsCAR (cpFock (n := n)) cmFock ∧
      CommutesCAR (0 : Fin n → Fin n → Module.End ℂ (Fock n)) cpFock cmFock := by sorry
