-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_poleVd_injective
-- name    : ReciprocityTheory.ChartRestriction.DS.poleVd_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:03.820652+00:00
-- url     : https://prove2.me/theorems/441a0883-4b81-55a9-94a7-87f3f0f10b93
-- title:
--   DS: pole Vd injective
-- statement:
--   The DS construction uses the pole Vd injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L166-L171

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

theorem ReciprocityTheory.ChartRestriction.DS.poleVd_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleVd μ) := by sorry
