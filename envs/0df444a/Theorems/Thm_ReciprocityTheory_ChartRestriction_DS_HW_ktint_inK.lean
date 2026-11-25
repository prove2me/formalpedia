-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_ktint_inK
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.ktint_inK
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:02.830653+00:00
-- url     : https://prove2.me/theorems/83f377b2-30c1-49a3-ad9d-ecc56af3c027
-- title:
--   HW: ktint in K
-- statement:
--   The HW construction uses the ktint in K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/KtintExpApplyOfEig.lean#L38-L53

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.ktint_inK (ε : Fin n → Bool) (a : Fin n) :
    inK ε (Complex.I • Matrix.single a a (1 : ℂ)) := by sorry
