-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_physSub_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.physSub_stable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:37.863294+00:00
-- url     : https://prove2.me/theorems/e5242bcf-2eb0-4164-8fe3-3f7602d48893
-- title:
--   DS: phys Sub stable
-- statement:
--   The DS construction uses the phys Sub stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L76-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem ReciprocityTheory.ChartRestriction.DS.physSub_stable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, eT E a b x ∈ physicalSubspace ε) ∧
      (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, diagE ε (eT E) cpT cmT a b x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp ε (eT E) cpT x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp' ε (eT E) cmT x ∈ physicalSubspace ε) ∧
      ∀ x ∈ physicalSubspace (N := N) ε, gradT x ∈ physicalSubspace ε := by sorry
