-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_locDensPullback
-- name    : ReciprocityTheory.AnForm.M.locDensPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:33.024106+00:00
-- url     : https://prove2.me/theorems/d2a7efb4-0893-481f-a5b1-8c905e48406a
-- title:
--   M: loc Dens Pullback
-- statement:
--   The M construction uses the loc Dens Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L49-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L49-L66

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
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
noncomputable section

theorem ReciprocityTheory.AnForm.M.locDensPullback : LocDensPullbackStatement := by sorry
