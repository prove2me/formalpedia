-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialRsmul
-- name    : ReciprocityTheory.AnForm.M.isPotentialRsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:56.612141+00:00
-- url     : https://prove2.me/theorems/3776dfa8-6958-425a-b2ed-a41213bf7ce3
-- title:
--   M: is Potential Rsmul
-- statement:
--   The M construction uses the is Potential Rsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L84-L86

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
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

theorem ReciprocityTheory.AnForm.M.isPotentialRsmul : IsPotentialRsmulStatement := by sorry
