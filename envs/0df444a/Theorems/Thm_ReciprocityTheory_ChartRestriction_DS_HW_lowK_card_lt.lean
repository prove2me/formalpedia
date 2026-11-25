-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowK_card_lt
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowK_card_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:27.449168+00:00
-- url     : https://prove2.me/theorems/f27a1f12-f14e-587a-ae62-a1b8bfee0d85
-- title:
--   HW: low K card lt
-- statement:
--   The HW construction uses the low K card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L67-L81

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowK_card_lt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card
      = a := by sorry
