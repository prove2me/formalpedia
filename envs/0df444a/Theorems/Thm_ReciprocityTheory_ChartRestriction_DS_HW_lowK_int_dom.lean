-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowK_int_dom
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lowK_int_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:14.874023+00:00
-- url     : https://prove2.me/theorems/6975673f-15bf-41d6-b49c-4433b5788f19
-- title:
--   HW: low K int dom
-- statement:
--   The HW construction uses the low K int dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L100-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HcParamGapGeIndex.lean#L100-L154

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.lowK_int_dom (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    (∀ a, ∃ m : ℤ, lowK ε lam a = m) ∧ ∀ a b, a < b → ε a = ε b → lowK ε lam b ≤ lowK ε lam a := by sorry
