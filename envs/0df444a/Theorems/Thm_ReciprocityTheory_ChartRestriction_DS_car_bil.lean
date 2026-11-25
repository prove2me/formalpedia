-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_bil
-- name    : ReciprocityTheory.ChartRestriction.DS.car_bil
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:06.162224+00:00
-- url     : https://prove2.me/theorems/ffbf066c-5bf2-54f2-95e9-64a690f5daa9
-- title:
--   DS: car bil
-- statement:
--   The DS construction uses the car bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L56-L61

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

theorem ReciprocityTheory.ChartRestriction.DS.car_bil {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (i a j b k c l d : Fin n) :
    cp i a * cm j b * (cp k c * cm l d) - cp k c * cm l d * (cp i a * cm j b) =
      (if j = k ∧ b = c then cp i a * cm l d else 0) - (if l = i ∧ d = a then cp k c * cm j b else 0) := by sorry
