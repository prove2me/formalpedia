-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_cpT
-- name    : ReciprocityTheory.ChartRestriction.DS.gradT_cpT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:57.315365+00:00
-- url     : https://prove2.me/theorems/9ef5e669-044c-55cf-be56-ef4d4ff4a874
-- title:
--   DS: grad T cp T
-- statement:
--   The DS construction uses the grad T cp T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean#L36-L39

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

theorem ReciprocityTheory.ChartRestriction.DS.gradT_cpT (i a : Fin n) : gradT (N := N) * cpT i a = -(cpT i a * gradT) := by sorry
