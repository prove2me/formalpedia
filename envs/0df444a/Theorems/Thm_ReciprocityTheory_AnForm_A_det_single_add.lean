-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_single_add
-- name    : ReciprocityTheory.AnForm.A.det_single_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:58.615609+00:00
-- url     : https://prove2.me/theorems/0315a967-2d4d-536a-b575-5ade8812a8f7
-- title:
--   A: det single add
-- statement:
--   The A construction uses the det single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L191-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L191-L211

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section

theorem ReciprocityTheory.AnForm.A.det_single_add {n : ℕ} (j : Fin (n + 1)) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (Matrix.single j j 1 + M).det = M.det + (M.submatrix j.succAbove j.succAbove).det := by sorry
