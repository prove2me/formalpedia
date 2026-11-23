-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mIntNonneg
-- name    : ReciprocityTheory.AnForm.M.mIntNonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:39.614805+00:00
-- url     : https://prove2.me/theorems/22e1dac9-61c8-4cd7-ba9e-6583646d54d4
-- title:
--   M: m Int Nonneg
-- statement:
--   The M construction uses the m Int Nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L156-L162

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
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
open scoped ContDiff ComplexOrder
noncomputable section

theorem ReciprocityTheory.AnForm.M.mIntNonneg : MIntNonnegStatement := by sorry
