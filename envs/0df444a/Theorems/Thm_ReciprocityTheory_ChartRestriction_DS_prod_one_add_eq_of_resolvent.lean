-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prod_one_add_eq_of_resolvent
-- name    : ReciprocityTheory.ChartRestriction.DS.prod_one_add_eq_of_resolvent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:17.634965+00:00
-- url     : https://prove2.me/theorems/9b9b67ae-66d8-4a09-8b73-b9a00352311e
-- title:
--   DS: prod one add eq of resolvent
-- statement:
--   The DS construction uses the prod one add eq of resolvent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L17-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L17-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.prod_one_add_eq_of_resolvent {ι : Type} [DecidableEq ι] (S : Finset ι) :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (a : ι → ℂ) (_ : Set.InjOn a S) (g : ι → R)
      (_ : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (a t - a s) • (g t * g s) = g t - g s),
      ∏ s ∈ S, (1 + g s) =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s := by sorry
