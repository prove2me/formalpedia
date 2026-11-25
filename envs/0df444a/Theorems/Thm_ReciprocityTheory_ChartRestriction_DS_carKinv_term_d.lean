-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d
-- name    : ReciprocityTheory.ChartRestriction.DS.carKinv_term_d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:58.527441+00:00
-- url     : https://prove2.me/theorems/b621f4c5-22e6-4168-8cf4-426f02d8674c
-- title:
--   DS: car Kinv term d
-- statement:
--   The DS construction uses the car Kinv term d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARKinv.lean#L103-L109

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

theorem ReciprocityTheory.ChartRestriction.DS.carKinv_term_d {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E c i * cp i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E c i * cp i c) =
      ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
        E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) := by sorry
