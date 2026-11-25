-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_eq
-- name    : ReciprocityTheory.AnForm.A.hessCof_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:14.309346+00:00
-- url     : https://prove2.me/theorems/b10805c2-c7bc-49f0-aa95-01b9fa2caea9
-- title:
--   A: hess Cof eq
-- statement:
--   The A construction uses the hess Cof eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L138-L140

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

theorem ReciprocityTheory.AnForm.A.hessCof_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (j k : Fin (n + 1)) :
    hessCof φ y j k = mdisc (Fin.cons (Matrix.single j k 1) fun i => hessMat (fderiv ℝ (fderiv ℝ (φ i)) y)) := by sorry
