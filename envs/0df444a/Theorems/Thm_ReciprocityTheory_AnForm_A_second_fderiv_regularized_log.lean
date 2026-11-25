-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_second_fderiv_regularized_log
-- name    : ReciprocityTheory.AnForm.A.second_fderiv_regularized_log
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:49.120828+00:00
-- url     : https://prove2.me/theorems/57ad9313-92d7-435b-b65a-918cd2e6de50
-- title:
--   A: second fderiv regularized log
-- statement:
--   The A construction uses the second fderiv regularized log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L41-L57

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.A.second_fderiv_regularized_log {ε : ℝ} (hε : 0 < ε) (ζ a b : ℂ) :
    fderiv ℝ (fderiv ℝ (gReg ε)) ζ a b =
      (‖ζ‖ ^ 2 + ε)⁻¹ * inner ℝ a b - 2 * inner ℝ ζ a * inner ℝ ζ b / (‖ζ‖ ^ 2 + ε) ^ 2 := by sorry
