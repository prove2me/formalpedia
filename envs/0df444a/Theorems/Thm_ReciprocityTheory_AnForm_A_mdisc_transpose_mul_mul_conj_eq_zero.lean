-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_transpose_mul_mul_conj_eq_zero
-- name    : ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:07.911893+00:00
-- url     : https://prove2.me/theorems/8995a909-67ad-4bcb-95bd-bf9e7cc3de86
-- title:
--   A: mdisc transpose mul mul conj eq zero
-- statement:
--   The A construction uses the mdisc transpose mul mul conj eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L253-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L253-L268

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

theorem ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj_eq_zero {E : ℕ} (J : Matrix (Fin E) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin E) (Fin E) ℂ) (w : Fin D → ℂ) (hw : w ≠ 0) (hJw : J *ᵥ w = 0) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = 0 := by sorry
