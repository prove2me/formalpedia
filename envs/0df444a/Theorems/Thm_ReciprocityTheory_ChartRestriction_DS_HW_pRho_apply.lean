-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pRho_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pRho_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:04.280393+00:00
-- url     : https://prove2.me/theorems/8637d749-83c4-4013-bb8a-cfa2d8199bb8
-- title:
--   HW: p Rho apply
-- statement:
--   The HW construction uses the p Rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L114-L116

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
variable (ε β)

theorem ReciprocityTheory.ChartRestriction.DS.HW.pRho_apply (k : KG ε) (p q : pIdx ε β) :
    ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) p q =
      toMK k p.1.1 q.1.1 * star (toMK k p.1.2 q.1.2) := by sorry
