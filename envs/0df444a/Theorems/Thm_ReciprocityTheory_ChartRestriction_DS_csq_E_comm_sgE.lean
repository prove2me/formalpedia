-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_E_comm_sgE
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_E_comm_sgE
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:08.277599+00:00
-- url     : https://prove2.me/theorems/af306afb-f33a-499d-be49-d6a34786afb7
-- title:
--   DS: csq E comm sg E
-- statement:
--   The DS construction uses the csq E comm sg E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqB.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqB.lean#L121-L133

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.csq_E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (x y a b : Fin n) :
    E x y * sgE ε cp cm a b = sgE ε cp cm a b * E x y := by sorry
