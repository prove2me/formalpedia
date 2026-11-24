-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_kTypeIntDom
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.kTypeIntDom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:59.675915+00:00
-- url     : https://prove2.me/theorems/3ebb5c0c-58e4-4902-8a17-001e2fa18750
-- title:
--   HW: k Type Int Dom
-- statement:
--   The HW construction uses the k Type Int Dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/InnerLowerSelf.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/InnerLowerSelf.lean#L46-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_InnerLowerSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.kTypeIntDom : KTypeIntDomStatement := by sorry
