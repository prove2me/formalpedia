-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_abs_le
-- name    : ReciprocityTheory.AnForm.A.gReg_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:07.756346+00:00
-- url     : https://prove2.me/theorems/9ac16d6d-14cd-4289-a45b-039ff1106275
-- title:
--   A: g Reg abs le
-- statement:
--   The A construction uses the g Reg abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L147-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L147-L163

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

theorem ReciprocityTheory.AnForm.A.gReg_abs_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {ζ : ℂ} (hζ : ζ ≠ 0) :
    |gReg ε ζ| ≤ |Real.log ‖ζ‖| + (1 / 2) * Real.log (‖ζ‖ ^ 2 + 1) := by sorry
