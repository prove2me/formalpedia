-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b
-- name    : P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:26.126938+00:00
-- url     : https://prove2.me/theorems/eadda427-a31f-44b9-9162-58562657bfeb
-- title:
--   P2 M Reciprocity Theory An Form A mdisc cons eq sum  cdfc9455009b: P2 M Reciprocity Theory An Form A mdisc cons eq sum  cdfc9455009b
-- statement:
--   The P2 M Reciprocity Theory An Form A mdisc cons eq sum  cdfc9455009b construction uses the P2 M Reciprocity Theory An Form A mdisc cons eq sum  cdfc9455009b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L117-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L117-L173

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

theorem P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k *
      mdisc (Fin.cons (Matrix.single j k 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by sorry

alias «ReciprocityTheory».«AnForm».«A».«mdisc_cons_eq_sum'» := P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b
