-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_conj_single
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_conj_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:58.907032+00:00
-- url     : https://prove2.me/theorems/c1c64602-d422-5eb2-b14a-d508945af9b9
-- title:
--   DS: tset conj single
-- statement:
--   The DS construction uses the tset conj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L49-L52

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

theorem ReciprocityTheory.ChartRestriction.DS.tset_conj_single (k : Matrix (Fin n) (Fin n) ℂ) (r d a b : Fin n) :
    (k * Matrix.single r d (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) a b = k a r * star (k b d) := by sorry
