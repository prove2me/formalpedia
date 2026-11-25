-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_pAdM_diag
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pAdM_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:49.488329+00:00
-- url     : https://prove2.me/theorems/1cc2ce3f-affd-5639-ba4c-e6991bf94165
-- title:
--   HW: p Plus p Ad M diag
-- statement:
--   The HW construction uses the p Plus p Ad M diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PPlusPWtInjective.lean#L22-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pAdM_diag (ε : Fin n → Bool) (β : Bool) (a : Fin n) :
    pAdM ε β a a = Matrix.diagonal fun p => ((pWt ε β p a : ℝ) : ℂ) := by sorry
