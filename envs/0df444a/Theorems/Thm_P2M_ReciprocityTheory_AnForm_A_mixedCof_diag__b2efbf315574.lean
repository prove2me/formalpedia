-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574
-- name    : P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:04.671905+00:00
-- url     : https://prove2.me/theorems/1181ca0f-ff03-4688-b8f2-f0c63a526864
-- title:
--   P2 M Reciprocity Theory An Form A mixed Cof diag  b2efbf315574: P2 M Reciprocity Theory An Form A mixed Cof diag  b2efbf315574
-- statement:
--   The P2 M Reciprocity Theory An Form A mixed Cof diag  b2efbf315574 construction uses the P2 M Reciprocity Theory An Form A mixed Cof diag  b2efbf315574 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L218-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L218-L244

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

theorem P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574 {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mdisc (Fin.cons (Matrix.single j j 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n + 1 : ℕ) : ℂ)) * mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by sorry

alias «ReciprocityTheory».«AnForm».«A».«mixedCof_diag'» := P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574
