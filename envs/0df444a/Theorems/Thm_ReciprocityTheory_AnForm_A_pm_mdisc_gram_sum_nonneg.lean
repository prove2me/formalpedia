-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_gram_sum_nonneg
-- name    : ReciprocityTheory.AnForm.A.pm_mdisc_gram_sum_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:27.551079+00:00
-- url     : https://prove2.me/theorems/977c5e38-b7a1-4379-b362-48e791a646c2
-- title:
--   A: pm mdisc gram sum nonneg
-- statement:
--   The A construction uses the pm mdisc gram sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L136-L138

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

theorem ReciprocityTheory.AnForm.A.pm_mdisc_gram_sum_nonneg (w : Fin D → ι → Fin D → ℂ) :
    0 ≤ ∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det := by sorry
