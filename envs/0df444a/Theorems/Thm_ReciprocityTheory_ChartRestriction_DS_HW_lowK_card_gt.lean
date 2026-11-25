-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowK_card_gt
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowK_card_gt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:19.930275+00:00
-- url     : https://prove2.me/theorems/75797ad7-c956-5227-b561-91be4066a55d
-- title:
--   HW: low K card gt
-- statement:
--   The HW construction uses the low K card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L51-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HcParamGapGeIndex
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowK_card_gt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => a < b ∧ ε b = ε a).card
      = n - 1 - a := by sorry
