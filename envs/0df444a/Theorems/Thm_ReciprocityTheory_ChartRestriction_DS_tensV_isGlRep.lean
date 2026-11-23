-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensV_isGlRep
-- name    : ReciprocityTheory.ChartRestriction.DS.tensV_isGlRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:06.27164+00:00
-- url     : https://prove2.me/theorems/fd506e8f-8cc0-40f0-bbe5-0112a04e4fa4
-- title:
--   DS: tens V is Gl Rep
-- statement:
--   The DS construction uses the tens V is Gl Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L63-L69

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

theorem ReciprocityTheory.ChartRestriction.DS.tensV_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensV E) := by sorry
