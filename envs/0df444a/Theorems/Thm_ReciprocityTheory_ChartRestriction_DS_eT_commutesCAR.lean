-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eT_commutesCAR
-- name    : ReciprocityTheory.ChartRestriction.DS.eT_commutesCAR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:46.329789+00:00
-- url     : https://prove2.me/theorems/f68bd6d4-7c70-4b4e-869a-71c6beb9759b
-- title:
--   DS: e T commutes CAR
-- statement:
--   The DS construction uses the e T commutes CAR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L71-L74

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

theorem ReciprocityTheory.ChartRestriction.DS.eT_commutesCAR (E : Fin n → Fin n → Module.End ℂ N) : CommutesCAR (eT E) cpT cmT := by sorry
