-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_rho_split
-- name    : ReciprocityTheory.ChartRestriction.DS.nsq_rho_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:36.770645+00:00
-- url     : https://prove2.me/theorems/9d37ba29-0b5b-4956-819a-68b3e1a60cb4
-- title:
--   DS: nsq rho split
-- statement:
--   The DS construction uses the nsq rho split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L123-L132

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

theorem ReciprocityTheory.ChartRestriction.DS.nsq_rho_split (ε : Fin n → Bool) : nsq (rho n) = nsq (rhoC ε) + nsq (rhoHol ε) := by sorry
