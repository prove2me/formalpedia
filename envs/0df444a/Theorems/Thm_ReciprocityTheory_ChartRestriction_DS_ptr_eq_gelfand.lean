-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ptr_eq_gelfand
-- name    : ReciprocityTheory.ChartRestriction.DS.ptr_eq_gelfand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:34.384565+00:00
-- url     : https://prove2.me/theorems/aeca15d6-233b-4578-95fb-44894712ad35
-- title:
--   DS: ptr eq gelfand
-- statement:
--   The DS construction uses the ptr eq gelfand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/PartialTrace.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/PartialTrace.lean#L53-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
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

theorem ReciprocityTheory.ChartRestriction.DS.ptr_eq_gelfand (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) : ptr (A ^ k) = gelfand T k := by sorry
