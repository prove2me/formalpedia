-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_gram_apply
-- name    : ReciprocityTheory.AnForm.A.pm_sum_gram_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:24.787318+00:00
-- url     : https://prove2.me/theorems/53517793-9d05-55eb-90b1-7fd4718d2635
-- title:
--   A: pm sum gram apply
-- statement:
--   The A construction uses the pm sum gram apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L16-L22

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

theorem ReciprocityTheory.AnForm.A.pm_sum_gram_apply (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) (a b : Fin D) :
    (∑ k ∈ S, pmGram w k) a b =
      ∑ p : Fin D × ι, (if p.1 ∈ S then (1 : ℂ) else 0) * (w p.1 p.2 a * star (w p.1 p.2 b)) := by sorry
