-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hc_param_gap_ge_index
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hc_param_gap_ge_index
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:45.784902+00:00
-- url     : https://prove2.me/theorems/dc72529b-c4f4-5624-8704-34d9e22efdf9
-- title:
--   HW: hc param gap ge index
-- statement:
--   The HW construction uses the hc param gap ge index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L13-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L13-L49

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hc_param_gap_ge_index (lam : Fin n → ℝ) (hlam : IsHCParam lam) (a b : Fin n) (hab : a ≤ b) :
    ((b : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam b := by sorry
