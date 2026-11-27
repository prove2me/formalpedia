-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_ratio_smul
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.ratio_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:48.120939+00:00
-- url     : https://prove2.me/theorems/9f5fe74c-aa37-4ebe-aada-e0ab13d61695
-- title:
--   Compatible Chart Operations: ratio smul
-- statement:
--   The Compatible Chart Operations construction uses the ratio smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L243-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L243-L247

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.ratio_smul (u v : ℂ × ℂ) {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ‖det2 (c • u) (d • v)‖ / (nrm2 (c • u) * nrm2 (d • v)) = ‖det2 u v‖ / (nrm2 u * nrm2 v) := by sorry
