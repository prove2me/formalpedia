-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_finsetSum_eq_sum_fun
-- name    : ReciprocityTheory.AnForm.A.det_finsetSum_eq_sum_fun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:58.933143+00:00
-- url     : https://prove2.me/theorems/2d13e11d-744f-4c20-a967-202cf327fad5
-- title:
--   A: det finset Sum eq sum fun
-- statement:
--   The A construction uses the det finset Sum eq sum fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L52-L66

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

theorem ReciprocityTheory.AnForm.A.det_finsetSum_eq_sum_fun {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (S : Finset (Fin D)) :
    (∑ k ∈ S, A k).det = ∑ r : Fin D → Fin D,
      if (∀ i, r i ∈ S) then (Matrix.of fun i => A (r i) i).det else 0 := by sorry
