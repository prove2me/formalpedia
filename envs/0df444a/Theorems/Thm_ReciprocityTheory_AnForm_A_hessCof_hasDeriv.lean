-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_hasDeriv
-- name    : ReciprocityTheory.AnForm.A.hessCof_hasDeriv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:50.450824+00:00
-- url     : https://prove2.me/theorems/3dc971a5-4d88-4679-b051-029a20083c79
-- title:
--   A: hess Cof has Deriv
-- statement:
--   The A construction uses the hess Cof has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L154-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L154-L204

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

theorem ReciprocityTheory.AnForm.A.hessCof_hasDeriv {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ)
    (hφ : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z) (j k : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => hessCof φ y j k) z ∧ ∀ u,
      fderiv ℝ (fun y => hessCof φ y j k) z u = ∑ i, mdisc (Function.update
        (Fin.cons (Matrix.single j k 1) fun l => hessC (φ l) z) i.succ
          (hessMat (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z u))) := by sorry
