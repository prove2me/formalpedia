-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_gReg
-- name    : ReciprocityTheory.AnForm.A.fderiv_gReg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:57.495793+00:00
-- url     : https://prove2.me/theorems/ddfc3ebc-9395-4ddc-bb82-d441e2d4d29a
-- title:
--   A: fderiv g Reg
-- statement:
--   The A construction uses the fderiv g Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L37-L39

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

theorem ReciprocityTheory.AnForm.A.fderiv_gReg {ε : ℝ} (hε : 0 < ε) :
    fderiv ℝ (gReg ε) = fun ζ => (‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ := by sorry
