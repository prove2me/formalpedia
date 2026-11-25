-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___eq_f40018ae65da
-- name    : P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___eq_f40018ae65da
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:35.11752+00:00
-- url     : https://prove2.me/theorems/b5981ad2-f8fb-506a-bdde-e87e2d6caa21
-- title:
--   P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   eq f40018ae65da: P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   eq f40018ae65da
-- statement:
--   The P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   eq f40018ae65da construction uses the P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   eq f40018ae65da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L135-L138

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

theorem P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___eq_f40018ae65da (a p : OnePoint ℂ) : fsPot.φ a p = Real.log (nrm2 (homogeneousLift a p)) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«CompatibleChartOperations».«fsPot_φ_eq» := P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___eq_f40018ae65da
