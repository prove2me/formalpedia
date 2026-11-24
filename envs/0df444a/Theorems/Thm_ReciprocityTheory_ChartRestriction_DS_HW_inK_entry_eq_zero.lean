-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_entry_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.inK_entry_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:55.425844+00:00
-- url     : https://prove2.me/theorems/554f7f99-6060-4be8-8b17-ab8fafbde107
-- title:
--   HW: in K entry eq zero
-- statement:
--   The HW construction uses the in K entry eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/SingleMulJmComm.lean#L13-L23

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.inK_entry_eq_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    {a b : Fin n} (hab : ε a ≠ ε b) : Y a b = 0 := by sorry
