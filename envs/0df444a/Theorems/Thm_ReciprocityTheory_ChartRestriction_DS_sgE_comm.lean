-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.sgE_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:09.780306+00:00
-- url     : https://prove2.me/theorems/0712a0ab-dbcd-40ba-bdb6-620425d8412d
-- title:
--   DS: sg E comm
-- statement:
--   The DS construction uses the sg E comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L138-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean#L138-L224

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

theorem ReciprocityTheory.ChartRestriction.DS.sgE_comm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b =
      (if b = c then sgE ε cp cm a d else 0) - (if d = a then sgE ε cp cm c b else 0) := by sorry
