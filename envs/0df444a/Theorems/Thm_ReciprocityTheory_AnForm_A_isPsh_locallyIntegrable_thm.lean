-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_isPsh_locallyIntegrable_thm
-- name    : ReciprocityTheory.AnForm.A.isPsh_locallyIntegrable_thm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:07:04.210465+00:00
-- url     : https://prove2.me/theorems/4df6929f-6ea1-5aa1-af78-9236db30c707
-- title:
--   A: is Psh locally Integrable thm
-- statement:
--   The A construction uses the is Psh locally Integrable thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L264-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L264-L265

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Set Filter Topology Real PshInh

theorem ReciprocityTheory.AnForm.A.isPsh_locallyIntegrable_thm : IsPsh_locallyIntegrableStatement := by sorry
