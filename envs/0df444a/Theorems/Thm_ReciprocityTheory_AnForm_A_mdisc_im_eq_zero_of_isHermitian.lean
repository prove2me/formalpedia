-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_im_eq_zero_of_isHermitian
-- name    : ReciprocityTheory.AnForm.A.mdisc_im_eq_zero_of_isHermitian
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:02.690974+00:00
-- url     : https://prove2.me/theorems/32990425-db95-41ce-8423-7fc545087672
-- title:
--   A: mdisc im eq zero of is Hermitian
-- statement:
--   The A construction uses the mdisc im eq zero of is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L207-L212

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.mdisc_im_eq_zero_of_isHermitian (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).IsHermitian) : (mdisc A).im = 0 := by sorry
