-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_ktint_exp_apply_of_eig
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.ktint_exp_apply_of_eig
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:41:49.868987+00:00
-- url     : https://prove2.me/theorems/a6cb1a35-f671-4664-afb2-ad9da1669e6c
-- title:
--   HW: ktint exp apply of eig
-- statement:
--   The HW construction uses the ktint exp apply of eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L14-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.ktint_exp_apply_of_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (c : ℂ) (v : E) (h : A v = c • v) :
    NormedSpace.exp A v = NormedSpace.exp c • v := by sorry
