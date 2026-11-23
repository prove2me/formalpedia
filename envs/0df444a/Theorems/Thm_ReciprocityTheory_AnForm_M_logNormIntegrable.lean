-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_logNormIntegrable
-- name    : ReciprocityTheory.AnForm.M.logNormIntegrable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:17.067323+00:00
-- url     : https://prove2.me/theorems/c49e4367-43cf-49d1-847e-0fe06ff5ce39
-- title:
--   M: log Norm Integrable
-- statement:
--   The M construction uses the log Norm Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L168-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L168-L169

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.M.logNormIntegrable : LogNormIntegrableStatement := by sorry
