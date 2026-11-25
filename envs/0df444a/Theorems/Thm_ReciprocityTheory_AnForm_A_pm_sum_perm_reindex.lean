-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_perm_reindex
-- name    : ReciprocityTheory.AnForm.A.pm_sum_perm_reindex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:47.522048+00:00
-- url     : https://prove2.me/theorems/5a5b4b90-01e1-47f8-82c2-3dfb97e2966e
-- title:
--   A: pm sum perm reindex
-- statement:
--   The A construction uses the pm sum perm reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L84-L109

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.AnForm.A.pm_sum_perm_reindex (w : Fin D → ι → Fin D → ℂ) :
    (D.factorial : ℂ) * ∑ g : Fin D → Fin D × ι,
        (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) =
      ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) := by sorry
