-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sg_cp_plus
-- name    : ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cp_plus
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:20.377897+00:00
-- url     : https://prove2.me/theorems/7323ac93-eca0-521b-ba7a-8dfef0c5dbd0
-- title:
--   DS: car Kinv sg cp plus
-- statement:
--   The DS construction uses the car Kinv sg cp plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L49-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cp_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = if b = i then cp a c else 0 := by sorry
