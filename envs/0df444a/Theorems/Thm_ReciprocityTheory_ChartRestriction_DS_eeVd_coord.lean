-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeVd_coord
-- name    : ReciprocityTheory.ChartRestriction.DS.eeVd_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:07.282691+00:00
-- url     : https://prove2.me/theorems/e218727d-0539-4302-ab70-79380f554fac
-- title:
--   DS: ee Vd coord
-- statement:
--   The DS construction uses the ee Vd coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L44-L46

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

theorem ReciprocityTheory.ChartRestriction.DS.eeVd_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (r : Fin n) :
    eeVd E f r = -∑ s, E r s (f s) := by sorry
