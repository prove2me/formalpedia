-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_logNormIntegrable_of
-- name    : ReciprocityTheory.AnForm.M.logNormIntegrable_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:47.02356+00:00
-- url     : https://prove2.me/theorems/41d12460-e9c0-41a5-89a8-23fcb3727b7f
-- title:
--   M: log Norm Integrable of
-- statement:
--   The M construction uses the log Norm Integrable of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L45-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LogInt.lean#L45-L166

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

theorem ReciprocityTheory.AnForm.M.logNormIntegrable_of (hLU : ReciprocityTheory.AnForm.A.LogUnitMonoLocIntStatement)
    (hD : LocDensContStatement) : LogNormIntegrableStatement := by sorry
