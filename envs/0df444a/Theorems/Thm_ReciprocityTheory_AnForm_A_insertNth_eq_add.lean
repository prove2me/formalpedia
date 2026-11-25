-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_insertNth_eq_add
-- name    : ReciprocityTheory.AnForm.A.insertNth_eq_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:04.535122+00:00
-- url     : https://prove2.me/theorems/b6cc8cf7-d8b5-4b8f-81e1-1d3aa324b57d
-- title:
--   A: insert Nth eq add
-- statement:
--   The A construction uses the insert Nth eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L11-L18

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

theorem ReciprocityTheory.AnForm.A.insertNth_eq_add {D : ℕ} (j : Fin (D + 1)) (w : Fin D → ℂ) (ζ : ℂ) :
    Fin.insertNth j ζ w = Fin.insertNth j (0 : ℂ) w + (Pi.single j ζ : Fin (D + 1) → ℂ) := by sorry
