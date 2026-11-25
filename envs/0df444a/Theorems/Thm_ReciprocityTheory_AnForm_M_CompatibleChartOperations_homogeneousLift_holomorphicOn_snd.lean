-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_homogeneousLift_holomorphicOn_snd
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.homogeneousLift_holomorphicOn_snd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:43.62777+00:00
-- url     : https://prove2.me/theorems/71220d30-94c5-4b61-8418-6d793bb22ee5
-- title:
--   Compatible Chart Operations: homogeneous Lift holomorphic On snd
-- statement:
--   The Compatible Chart Operations construction uses the homogeneous Lift holomorphic On snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L214-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L214-L241

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.homogeneousLift_holomorphicOn_snd (a : OnePoint ℂ) : p1.HoloOn (fsPot.U a) (fun p => (homogeneousLift a p).2) := by sorry
