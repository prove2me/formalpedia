-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_sum_finset_fin_succ
-- name    : ReciprocityTheory.AnForm.A.sum_finset_fin_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:18.743734+00:00
-- url     : https://prove2.me/theorems/e7017938-0d40-4c39-8dc9-be9cd84cd7bd
-- title:
--   A: sum finset fin succ
-- statement:
--   The A construction uses the sum finset fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L175-L189

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

theorem ReciprocityTheory.AnForm.A.sum_finset_fin_succ {β : Type*} [AddCommMonoid β] {n : ℕ} (g : Finset (Fin (n + 1)) → β) :
    ∑ S, g S = ∑ S : Finset (Fin n),
      (g (S.map (Fin.succEmb n)) + g (insert 0 (S.map (Fin.succEmb n)))) := by sorry
