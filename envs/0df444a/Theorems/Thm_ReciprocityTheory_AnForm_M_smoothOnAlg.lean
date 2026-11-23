-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_smoothOnAlg
-- name    : ReciprocityTheory.AnForm.M.smoothOnAlg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:42.162524+00:00
-- url     : https://prove2.me/theorems/f73bd1ed-c1ba-426f-9f3b-c263409fafae
-- title:
--   M: smooth On Alg
-- statement:
--   The M construction uses the smooth On Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L19-L23

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

theorem ReciprocityTheory.AnForm.M.smoothOnAlg : SmoothOnAlgStatement := by sorry
