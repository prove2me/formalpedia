-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_poleV_injective
-- name    : ReciprocityTheory.ChartRestriction.DS.poleV_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:54.812524+00:00
-- url     : https://prove2.me/theorems/9deb445f-7c22-44be-99c2-2355b889eae7
-- title:
--   DS: pole V injective
-- statement:
--   The DS construction uses the pole V injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L159-L164

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

theorem ReciprocityTheory.ChartRestriction.DS.poleV_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleV μ) := by sorry
