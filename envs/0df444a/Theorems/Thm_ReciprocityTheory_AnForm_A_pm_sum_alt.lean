-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_alt
-- name    : ReciprocityTheory.AnForm.A.pm_sum_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:05.10853+00:00
-- url     : https://prove2.me/theorems/48216c5a-7563-5898-897f-deb91bde6e69
-- title:
--   A: pm sum alt
-- statement:
--   The A construction uses the pm sum alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L71-L77

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

theorem ReciprocityTheory.AnForm.A.pm_sum_alt (g : Fin D → Fin D × ι) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if ∀ a, (g a).1 ∈ S then 1 else 0) =
      (pmWt g : ℂ) := by sorry
