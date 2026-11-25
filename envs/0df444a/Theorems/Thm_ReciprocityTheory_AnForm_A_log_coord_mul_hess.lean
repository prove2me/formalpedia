-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_log_coord_mul_hess
-- name    : ReciprocityTheory.AnForm.A.log_coord_mul_hess
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:38.57364+00:00
-- url     : https://prove2.me/theorems/c4aa7379-e957-4dca-a06d-88d8d5da00d0
-- title:
--   A: log coord mul hess
-- statement:
--   The A construction uses the log coord mul hess property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L192-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L192-L216

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

theorem ReciprocityTheory.AnForm.A.log_coord_mul_hess {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) (v w : Fin (D + 1) → ℂ)
    (h : v j = 0 ∨ w j = 0) :
    Integrable (fun z => Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w) ∧
      ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0 := by sorry
