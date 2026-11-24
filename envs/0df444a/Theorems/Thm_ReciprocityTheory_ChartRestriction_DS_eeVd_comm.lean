-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeVd_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.eeVd_comm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:24.348721+00:00
-- url     : https://prove2.me/theorems/0e5d81d9-3078-49ad-9617-e14723bb1fb5
-- title:
--   DS: ee Vd comm
-- statement:
--   The DS construction uses the ee Vd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L122-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.eeVd_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensVd E a b * eeVd E = eeVd E * tensVd E a b := by sorry
