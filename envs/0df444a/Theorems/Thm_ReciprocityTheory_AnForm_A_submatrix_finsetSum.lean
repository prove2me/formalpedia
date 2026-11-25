-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_submatrix_finsetSum
-- name    : ReciprocityTheory.AnForm.A.submatrix_finsetSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:15.553902+00:00
-- url     : https://prove2.me/theorems/4bad5a8b-1d94-4073-a0d5-2bd4c1f14743
-- title:
--   A: submatrix finset Sum
-- statement:
--   The A construction uses the submatrix finset Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L213-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L213-L216

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

theorem ReciprocityTheory.AnForm.A.submatrix_finsetSum {ι : Type*} {n m : ℕ} (f : Fin m → Fin n)
    (B : ι → Matrix (Fin n) (Fin n) ℂ) (S : Finset ι) :
    (∑ k ∈ S, B k).submatrix f f = ∑ k ∈ S, (B k).submatrix f f := by sorry
