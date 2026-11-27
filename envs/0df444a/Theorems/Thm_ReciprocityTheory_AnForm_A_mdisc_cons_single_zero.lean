-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_single_zero
-- name    : ReciprocityTheory.AnForm.A.mdisc_cons_single_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:49.726989+00:00
-- url     : https://prove2.me/theorems/74da2bcb-100f-5187-b58e-f81957b2fe02
-- title:
--   A: mdisc cons single zero
-- statement:
--   The A construction uses the mdisc cons single zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L346-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L346-L383

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.mdisc_cons_single_zero {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (Matrix.single 0 0 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix Fin.succ Fin.succ) := by sorry
