-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_prho_kron_sub
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.prho_kron_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:39.244639+00:00
-- url     : https://prove2.me/theorems/79e678bb-3e13-4433-bbaa-faa234ff3708
-- title:
--   HW: prho kron sub
-- statement:
--   The HW construction uses the prho kron sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean#L29-L31

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.prho_kron_sub {ι κ : Type*} (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by sorry
