-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_multiplicity_one_hypotheses_hold
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.multiplicity_one_hypotheses_hold
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:28.839328+00:00
-- url     : https://prove2.me/theorems/274823b7-ed92-42f0-aa55-35a6d1ad4221
-- title:
--   Mult1: multiplicity one hypotheses hold
-- statement:
--   The Mult1 construction uses the multiplicity one hypotheses hold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/InHolds.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/InHolds.lean#L7-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergHaarFactsHold
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_InHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.multiplicity_one_hypotheses_hold : UnitaryGroupStructuralFacts := by sorry
