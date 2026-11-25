-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_combd
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_combd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:33.729802+00:00
-- url     : https://prove2.me/theorems/6fb82826-71c5-5a73-8b8c-9022fe575746
-- title:
--   DS: tset combd
-- statement:
--   The DS construction uses the tset combd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L77-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L77-L96

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

theorem ReciprocityTheory.ChartRestriction.DS.tset_combd {H : Type*} [AddCommGroup H] [Module ℂ H] (k : Fin n → Fin n → ℂ)
    (hu : ∀ s b, ∑ d, k s d * star (k b d) = if s = b then 1 else 0) (X : Fin n → Fin n → Fin n → H)
    (r : Fin n) :
    ∑ d, star (k r d) • ∑ s, ∑ a, ∑ b, (k a d * star (k b s)) • X a b s =
      ∑ s, ∑ b, star (k b s) • X r b s := by sorry
