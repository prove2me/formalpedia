-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_sum_smul_eq_sum_mdisc
-- name    : ReciprocityTheory.AnForm.A.det_sum_smul_eq_sum_mdisc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:38.394941+00:00
-- url     : https://prove2.me/theorems/60db3d5a-7d6b-5437-b4c0-59529dfeb9d7
-- title:
--   A: det sum smul eq sum mdisc
-- statement:
--   The A construction uses the det sum smul eq sum mdisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L135-L142

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

theorem ReciprocityTheory.AnForm.A.det_sum_smul_eq_sum_mdisc {m : ℕ} (c : Fin m → ℂ)
    (A : Fin m → Matrix (Fin D) (Fin D) ℂ) :
    (∑ j, c j • A j).det = ∑ f : Fin D → Fin m, (∏ k, c (f k)) * mdisc (A ∘ f) := by sorry
