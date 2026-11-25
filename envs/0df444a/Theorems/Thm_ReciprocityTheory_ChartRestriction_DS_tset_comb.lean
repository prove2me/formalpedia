-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_comb
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_comb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:39.787165+00:00
-- url     : https://prove2.me/theorems/7bf770fc-9668-5adb-a410-9b4fc5ea1370
-- title:
--   DS: tset comb
-- statement:
--   The DS construction uses the tset comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L59-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L59-L75

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

theorem ReciprocityTheory.ChartRestriction.DS.tset_comb {H : Type*} [AddCommGroup H] [Module ℂ H] (k : Fin n → Fin n → ℂ)
    (hu : ∀ s b, ∑ d, k s d * star (k b d) = if s = b then 1 else 0) (X : Fin n → Fin n → Fin n → H)
    (s : Fin n) :
    ∑ d, k s d • ∑ r, ∑ a, ∑ b, (k a r * star (k b d)) • X a b r = ∑ r, ∑ a, k a r • X a s r := by sorry
