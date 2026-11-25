-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_adDFull_zero_out
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.adDFull_zero_out
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:16.801038+00:00
-- url     : https://prove2.me/theorems/21662577-d287-5ddc-978e-96c07b11e7c0
-- title:
--   HW: ad DFull zero out
-- statement:
--   The HW construction uses the ad DFull zero out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L69-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}

theorem ReciprocityTheory.ChartRestriction.DS.HW.adDFull_zero_out {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adDFull X p k = 0 := by sorry
