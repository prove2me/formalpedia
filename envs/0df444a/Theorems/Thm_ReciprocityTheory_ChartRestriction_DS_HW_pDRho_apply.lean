-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pDRho_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pDRho_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:03.187784+00:00
-- url     : https://prove2.me/theorems/b5ad6798-7524-4302-af63-95bd765d16de
-- title:
--   HW: p DRho apply
-- statement:
--   The HW construction uses the p DRho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L131-L133

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pDRho_apply (X : Matrix (Fin n) (Fin n) ℂ) (p q : pIdx ε β) :
    pDRho ε β X p q = X p.1.1 q.1.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.1.2 q.1.2 -
      (1 : Matrix (Fin n) (Fin n) ℂ) p.1.1 q.1.1 * X q.1.2 p.1.2 := by sorry
