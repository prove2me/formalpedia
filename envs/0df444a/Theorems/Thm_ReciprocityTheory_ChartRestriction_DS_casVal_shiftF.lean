-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casVal_shiftF
-- name    : ReciprocityTheory.ChartRestriction.DS.casVal_shiftF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:11.780477+00:00
-- url     : https://prove2.me/theorems/1df7b7e7-12b5-4290-9933-8a65ee1c2713
-- title:
--   DS: cas Val shift F
-- statement:
--   The DS construction uses the cas Val shift F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L297-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L297-L301

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

theorem ReciprocityTheory.ChartRestriction.DS.casVal_shiftF (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    ((casVal lam + n : ℝ) : ℂ) + 2 * poleF dual lam s = ((casVal (shiftF dual lam s) : ℝ) : ℂ) := by sorry
