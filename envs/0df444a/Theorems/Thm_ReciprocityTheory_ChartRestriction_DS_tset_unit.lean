-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_unit
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:40.560356+00:00
-- url     : https://prove2.me/theorems/651c67d6-b893-5f59-989b-171ae7aa6e42
-- title:
--   DS: tset unit
-- statement:
--   The DS construction uses the tset unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L54-L57

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

theorem ReciprocityTheory.ChartRestriction.DS.tset_unit {k : Matrix (Fin n) (Fin n) ℂ} (hu : k * kᴴ = 1) (s b : Fin n) :
    ∑ d, k s d * star (k b d) = if s = b then 1 else 0 := by sorry
