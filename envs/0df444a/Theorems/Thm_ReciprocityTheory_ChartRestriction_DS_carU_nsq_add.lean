-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carU_nsq_add
-- name    : ReciprocityTheory.ChartRestriction.DS.carU_nsq_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:17.369814+00:00
-- url     : https://prove2.me/theorems/912f383b-1f0e-49b6-8dcd-ee230c5d9fa0
-- title:
--   DS: car U nsq add
-- statement:
--   The DS construction uses the car U nsq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L114-L118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
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

theorem ReciprocityTheory.ChartRestriction.DS.carU_nsq_add (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by sorry
