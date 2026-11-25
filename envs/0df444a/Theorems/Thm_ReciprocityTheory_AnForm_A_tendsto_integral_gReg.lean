-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tendsto_integral_gReg
-- name    : ReciprocityTheory.AnForm.A.tendsto_integral_gReg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:50.009193+00:00
-- url     : https://prove2.me/theorems/818cebf6-1ec9-5c42-aabb-8d7dc230a7fd
-- title:
--   A: tendsto integral g Reg
-- statement:
--   The A construction uses the tendsto integral g Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L177-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L177-L204

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

theorem ReciprocityTheory.AnForm.A.tendsto_integral_gReg {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hFc : HasCompactSupport F)
    (hlog : LocallyIntegrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖) volume) :
    Tendsto (fun k : ℕ => ∫ z, gReg (1 / ((k : ℝ) + 1)) (z i) * F z) atTop
      (𝓝 (∫ z, Real.log ‖z i‖ * F z)) := by sorry
