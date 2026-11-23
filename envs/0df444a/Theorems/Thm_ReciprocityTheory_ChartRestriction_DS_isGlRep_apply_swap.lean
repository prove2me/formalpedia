-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isGlRep_apply_swap
-- name    : ReciprocityTheory.ChartRestriction.DS.isGlRep_apply_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:43.339166+00:00
-- url     : https://prove2.me/theorems/aabd2bd5-a162-42ee-9654-1de8a54328bb
-- title:
--   DS: is Gl Rep apply swap
-- statement:
--   The DS construction uses the is Gl Rep apply swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L52-L57

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

theorem ReciprocityTheory.ChartRestriction.DS.isGlRep_apply_swap {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b c d : Fin n) (v : M) :
    E a b (E c d v) = E c d (E a b v) + ((if b = c then E a d v else 0) - (if d = a then E c b v else 0)) := by sorry
