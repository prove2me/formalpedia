-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_xiExists_of_in
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of_in
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:03.837344+00:00
-- url     : https://prove2.me/theorems/f7be3693-0052-49cb-9835-197b97536bba
-- title:
--   Xi: xi Exists of in
-- statement:
--   The Xi construction uses the xi Exists of in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExistsOfIn.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiExistsOfIn.lean#L13-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExists2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergHaarFactsHold
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntStepOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FormulaFOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_OsOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_AStepSuccOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MeasurableHaarKernelTriple
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_BStepSuccOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExistsOfIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi

theorem ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of_in (h : InductiveHeisenbergInputs) : Formalism.FourierDecayAlt.B.XiExists := by sorry
