-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eT_isGlRep
-- name    : ReciprocityTheory.ChartRestriction.DS.eT_isGlRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:08.467594+00:00
-- url     : https://prove2.me/theorems/14dca591-498c-41e5-9e17-1a4ff094b994
-- title:
--   DS: e T is Gl Rep
-- statement:
--   The DS construction uses the e T is Gl Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L49-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem ReciprocityTheory.ChartRestriction.DS.eT_isGlRep {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) : IsGlRep (eT (n := n) E) := by sorry
