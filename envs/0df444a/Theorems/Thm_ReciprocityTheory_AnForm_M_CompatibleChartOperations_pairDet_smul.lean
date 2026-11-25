-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairDet_smul
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:18.333085+00:00
-- url     : https://prove2.me/theorems/4801e6bd-6a3a-4cb0-b9d4-329694aabce8
-- title:
--   Compatible Chart Operations: pair Det smul
-- statement:
--   The Compatible Chart Operations construction uses the pair Det smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L122-L124

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_smul (c d : ℂ) (u v : ℂ × ℂ) : det2 (c • u) (d • v) = c * d * det2 u v := by sorry
