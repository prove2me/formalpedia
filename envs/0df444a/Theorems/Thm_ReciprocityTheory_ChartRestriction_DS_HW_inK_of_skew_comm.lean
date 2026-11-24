-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_of_skew_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.inK_of_skew_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:29.347503+00:00
-- url     : https://prove2.me/theorems/7e56cfb6-6ee1-4879-975c-ede8ba891478
-- title:
--   HW: in K of skew comm
-- statement:
--   The HW construction uses the in K of skew comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L61-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.inK_of_skew_comm {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h1 : Xᴴ = -X)
    (h2 : X * Jm ε = Jm ε * X) : inK ε X := by sorry
