-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_green_of_poincareLelongHyperplane
-- name    : ReciprocityTheory.AnForm.A.green_of_poincareLelongHyperplane
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:44.018052+00:00
-- url     : https://prove2.me/theorems/4c83fd51-ee4c-548b-b87a-b2183d369ba7
-- title:
--   A: green of poincare Lelong Hyperplane
-- statement:
--   The A construction uses the green of poincare Lelong Hyperplane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenOfPoincareLelongHyperplane.lean#L71-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenOfPoincareLelongHyperplane.lean#L71-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.A.green_of_poincareLelongHyperplane (h : PoincareLelongHyperplane) (u : (Fin 1 → ℂ) → ℝ) (hu : ContDiff ℝ 3 u)
    (hcs : HasCompactSupport u) :
    Integrable (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) ∧
      ∫ z : Fin 1 → ℂ, Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z = u 0 := by sorry
