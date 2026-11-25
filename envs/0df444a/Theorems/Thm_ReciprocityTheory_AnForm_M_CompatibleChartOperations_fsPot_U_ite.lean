-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot_U_ite
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.fsPot_U_ite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:07.955009+00:00
-- url     : https://prove2.me/theorems/85cb4222-2dec-4be0-afeb-a56d0ea06399
-- title:
--   Compatible Chart Operations: fs Pot U ite
-- statement:
--   The Compatible Chart Operations construction uses the fs Pot U ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L77-L78

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.fsPot_U_ite (a : OnePoint ℂ) :
    fsPot.U a = if a = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source := by sorry
