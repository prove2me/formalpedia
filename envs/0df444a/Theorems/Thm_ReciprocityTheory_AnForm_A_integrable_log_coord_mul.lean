-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_log_coord_mul
-- name    : ReciprocityTheory.AnForm.A.integrable_log_coord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:52.533142+00:00
-- url     : https://prove2.me/theorems/8e3cf1ac-2d9c-45d8-bf39-4ace4f231195
-- title:
--   A: integrable log coord mul
-- statement:
--   The A construction uses the integrable log coord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L123-L128

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

theorem ReciprocityTheory.AnForm.A.integrable_log_coord_mul {D : ℕ} (j : Fin (D + 1)) {φ : (Fin (D + 1) → ℂ) → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * φ z) := by sorry
