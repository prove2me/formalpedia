-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_log_coord_mul_fderiv
-- name    : ReciprocityTheory.AnForm.A.integral_log_coord_mul_fderiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:17.335837+00:00
-- url     : https://prove2.me/theorems/034d29e5-5f7e-48df-9c5d-0b7e8b4bf7c7
-- title:
--   A: integral log coord mul fderiv
-- statement:
--   The A construction uses the integral log coord mul fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L130-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L130-L190

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section

theorem ReciprocityTheory.AnForm.A.integral_log_coord_mul_fderiv {D : ℕ} (j : Fin (D + 1)) {g : (Fin (D + 1) → ℂ) → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) {x : Fin (D + 1) → ℂ} (hx : x j = 0) :
    ∫ z, Real.log ‖z j‖ * fderiv ℝ g z x = 0 := by sorry
