-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_isPsh_iff_isLeviPsh_thm
-- name    : ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:10.172794+00:00
-- url     : https://prove2.me/theorems/7b23d3d4-f98e-4624-a385-b4dd815c0168
-- title:
--   A: is Psh iff is Levi Psh thm
-- statement:
--   The A construction uses the is Psh iff is Levi Psh thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L210-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L210-L210

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

theorem ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm : IsPsh_iff_isLeviPshStatement := by sorry
