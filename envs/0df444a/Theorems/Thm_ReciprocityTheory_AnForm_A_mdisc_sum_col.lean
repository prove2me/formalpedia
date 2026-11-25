-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_sum_col
-- name    : ReciprocityTheory.AnForm.A.mdisc_sum_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:47.197886+00:00
-- url     : https://prove2.me/theorems/b76ab16c-60ac-461d-a651-20472409c26d
-- title:
--   A: mdisc sum col
-- statement:
--   The A construction uses the mdisc sum col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L254-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L254-L263

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

theorem ReciprocityTheory.AnForm.A.mdisc_sum_col {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ k a b, S k a b = S b a k) :
    ∑ k, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S k)) = 0 := by sorry
