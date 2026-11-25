-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sg_cp_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cp_minus
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:57.252435+00:00
-- url     : https://prove2.me/theorems/0e26ff7f-9c08-50e1-bfce-471a7db98cba
-- title:
--   DS: car Kinv sg cp minus
-- statement:
--   The DS construction uses the car Kinv sg cp minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L61-L73

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

theorem ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cp_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = -(if a = c then cp i b else 0) := by sorry
