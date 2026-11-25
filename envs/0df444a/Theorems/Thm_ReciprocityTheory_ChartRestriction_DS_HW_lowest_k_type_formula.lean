-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowest_k_type_formula
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowest_k_type_formula
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:51.928885+00:00
-- url     : https://prove2.me/theorems/3461b789-1400-425e-84f9-0055c1f85c57
-- title:
--   HW: lowest k type formula
-- statement:
--   The HW construction uses the lowest k type formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L83-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L83-L98

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowest_k_type_formula (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + ((n : ℝ) - 1) / 2 - (a : ℕ)
      - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := by sorry
