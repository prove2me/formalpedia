-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_offdiag_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.uq_offdiag_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:29:38.324365+00:00
-- url     : https://prove2.me/theorems/e04e3b89-0728-4095-9e60-d85cef567199
-- title:
--   HW: uq offdiag zero
-- statement:
--   The HW construction uses the uq offdiag zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Unique.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/Unique.lean#L14-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.uq_offdiag_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    {a b : Fin n} (hab : ε a ≠ ε b) : X a b = 0 := by sorry
