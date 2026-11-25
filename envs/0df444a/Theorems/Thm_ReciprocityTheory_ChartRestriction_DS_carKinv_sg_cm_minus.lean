-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sg_cm_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cm_minus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:50.245804+00:00
-- url     : https://prove2.me/theorems/f0e83e07-02d3-54ba-84bb-5d04020c32ae
-- title:
--   DS: car Kinv sg cm minus
-- statement:
--   The DS construction uses the car Kinv sg cm minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L89-L101

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

theorem ReciprocityTheory.ChartRestriction.DS.carKinv_sg_cm_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = if c = b then cm i a else 0 := by sorry
