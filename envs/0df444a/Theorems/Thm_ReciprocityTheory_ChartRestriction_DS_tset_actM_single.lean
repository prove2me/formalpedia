-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_actM_single
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_actM_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:53.430392+00:00
-- url     : https://prove2.me/theorems/71f0ca42-7599-408c-aa52-051e7c8b03c1
-- title:
--   DS: tset act M single
-- statement:
--   The DS construction uses the tset act M single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L44-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
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
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.tset_actM_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (r d : Fin n) : actM E (Matrix.single r d (1 : ℂ)) = E r d := by sorry
