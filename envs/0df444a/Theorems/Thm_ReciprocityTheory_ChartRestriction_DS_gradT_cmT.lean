-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_cmT
-- name    : ReciprocityTheory.ChartRestriction.DS.gradT_cmT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:50.759281+00:00
-- url     : https://prove2.me/theorems/f5300b6e-b3cb-460a-b39f-4c2c5487957d
-- title:
--   DS: grad T cm T
-- statement:
--   The DS construction uses the grad T cm T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L41-L44

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

theorem ReciprocityTheory.ChartRestriction.DS.gradT_cmT (i a : Fin n) : gradT (N := N) * cmT i a = -(cmT i a * gradT) := by sorry
