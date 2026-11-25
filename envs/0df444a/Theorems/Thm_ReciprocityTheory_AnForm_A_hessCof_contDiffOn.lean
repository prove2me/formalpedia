-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_contDiffOn
-- name    : ReciprocityTheory.AnForm.A.hessCof_contDiffOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:02.11862+00:00
-- url     : https://prove2.me/theorems/241e352e-c35c-5a42-9afe-8bdb5292dc54
-- title:
--   A: hess Cof cont Diff On
-- statement:
--   The A construction uses the hess Cof cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L277-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L277-L290

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.A.hessCof_contDiffOn {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ))
    (hU : IsOpen U) (m : ℕ) (hφ : ∀ i, ContDiffOn ℝ (m + 2) (φ i) U) (j k : Fin (n + 1)) :
    ContDiffOn ℝ m (fun y => hessCof φ y j k) U := by sorry
