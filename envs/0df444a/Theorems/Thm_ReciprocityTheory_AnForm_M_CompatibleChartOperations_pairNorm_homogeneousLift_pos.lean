-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairNorm_homogeneousLift_pos
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairNorm_homogeneousLift_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:36.136559+00:00
-- url     : https://prove2.me/theorems/be23e939-3f6d-5fa0-8b93-9910ee07abc5
-- title:
--   Compatible Chart Operations: pair Norm homogeneous Lift pos
-- statement:
--   The Compatible Chart Operations construction uses the pair Norm homogeneous Lift pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L130-L133

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairNorm_homogeneousLift_pos (a p : OnePoint ℂ) : 0 < nrm2 (homogeneousLift a p) := by sorry
