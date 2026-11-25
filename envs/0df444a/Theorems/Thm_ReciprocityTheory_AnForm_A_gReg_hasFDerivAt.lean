-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_hasFDerivAt
-- name    : ReciprocityTheory.AnForm.A.gReg_hasFDerivAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:39.795019+00:00
-- url     : https://prove2.me/theorems/ec4bc35d-fd03-430b-a3d7-18569fa52a09
-- title:
--   A: g Reg has FDeriv At
-- statement:
--   The A construction uses the g Reg has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L28-L35

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

theorem ReciprocityTheory.AnForm.A.gReg_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    HasFDerivAt (gReg ε) ((‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ) ζ := by sorry
