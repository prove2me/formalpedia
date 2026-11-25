-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairDet_homogeneousLift_same
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_homogeneousLift_same
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:42.018544+00:00
-- url     : https://prove2.me/theorems/22032b1f-dd20-47a7-9667-205d6a2c47ac
-- title:
--   Compatible Chart Operations: pair Det homogeneous Lift same
-- statement:
--   The Compatible Chart Operations construction uses the pair Det homogeneous Lift same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L175-L183

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
open scoped Classical

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_homogeneousLift_same (a p q : OnePoint ℂ) :
    det2 (homogeneousLift a p) (homogeneousLift a q) = (if a = ∞ then 1 else -1) * (chartCoordAt a p - chartCoordAt a q) := by sorry
