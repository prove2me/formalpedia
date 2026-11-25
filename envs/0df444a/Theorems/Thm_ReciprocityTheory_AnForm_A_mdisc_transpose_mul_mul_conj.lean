-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_transpose_mul_mul_conj
-- name    : ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:41.82196+00:00
-- url     : https://prove2.me/theorems/adc37298-f2d0-4c1f-9edc-e19591edda08
-- title:
--   A: mdisc transpose mul mul conj
-- statement:
--   The A construction uses the mdisc transpose mul mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L245-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L245-L251

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

theorem ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj (J : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = (Complex.normSq J.det : ℂ) * mdisc A := by sorry
