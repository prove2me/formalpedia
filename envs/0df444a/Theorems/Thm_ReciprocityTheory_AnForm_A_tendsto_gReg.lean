-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tendsto_gReg
-- name    : ReciprocityTheory.AnForm.A.tendsto_gReg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:30.308178+00:00
-- url     : https://prove2.me/theorems/049fb0c0-1670-56bf-bda2-b59fcf7f6201
-- title:
--   A: tendsto g Reg
-- statement:
--   The A construction uses the tendsto g Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L165-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L165-L175

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

theorem ReciprocityTheory.AnForm.A.tendsto_gReg {ζ : ℂ} (hζ : ζ ≠ 0) :
    Tendsto (fun k : ℕ => gReg (1 / ((k : ℝ) + 1)) ζ) atTop (𝓝 (Real.log ‖ζ‖)) := by sorry
