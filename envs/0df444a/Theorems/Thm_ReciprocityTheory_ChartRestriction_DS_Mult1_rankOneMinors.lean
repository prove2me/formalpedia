-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_rankOneMinors
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.rankOneMinors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:20.324041+00:00
-- url     : https://prove2.me/theorems/e6a81a60-6e86-501a-b727-1b528b124ff1
-- title:
--   Mult1: rank One Minors
-- statement:
--   The Mult1 construction uses the rank One Minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/JRankOne.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/JRankOne.lean#L5-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.rankOneMinors : RankOneMinors := by sorry
