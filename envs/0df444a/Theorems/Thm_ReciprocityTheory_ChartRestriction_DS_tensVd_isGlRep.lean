-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensVd_isGlRep
-- name    : ReciprocityTheory.ChartRestriction.DS.tensVd_isGlRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:06.114643+00:00
-- url     : https://prove2.me/theorems/71501c10-0862-4ac1-bd49-234d77186178
-- title:
--   DS: tens Vd is Gl Rep
-- statement:
--   The DS construction uses the tens Vd is Gl Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L71-L77

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

theorem ReciprocityTheory.ChartRestriction.DS.tensVd_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensVd E) := by sorry
