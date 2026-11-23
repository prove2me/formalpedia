-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq_zero
-- name    : ReciprocityTheory.AnForm.A.maDens_cons_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:56.700867+00:00
-- url     : https://prove2.me/theorems/a21d3852-6a6c-46d5-8ac3-7ed41e81f9f7
-- title:
--   A: ma Dens cons eq zero
-- statement:
--   The A construction uses the ma Dens cons eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L251-L255

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
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.maDens_cons_eq_zero {v : (Fin (n + 1) → ℂ) → ℝ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {z : Fin (n + 1) → ℂ} (hz : z ∉ tsupport v) : maDens (Fin.cons v φ) z = 0 := by sorry
