-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367
-- name    : P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:42.602286+00:00
-- url     : https://prove2.me/theorems/52a6cb88-12a3-5c2e-b639-83c79bbc4ee0
-- title:
--   P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   ite c35675c87367: P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   ite c35675c87367
-- statement:
--   The P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   ite c35675c87367 construction uses the P2 M Reciprocity Theory An Form M Compatible Chart Operations fs Pot   ite c35675c87367 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L81-L82

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

theorem P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367 (a p : OnePoint ℂ) : fsPot.φ a p = if a = ∞ then (1 / 2) * Real.log (1 + ‖crd1 p‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 p‖ ^ 2) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«CompatibleChartOperations».«fsPot_φ_ite» := P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367
