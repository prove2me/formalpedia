-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_comp_perm
-- name    : ReciprocityTheory.AnForm.A.mdisc_comp_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:28.714035+00:00
-- url     : https://prove2.me/theorems/6d6c683a-3179-4b67-b621-1b82e1b593c2
-- title:
--   A: mdisc comp perm
-- statement:
--   The A construction uses the mdisc comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L84-L88

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

theorem ReciprocityTheory.AnForm.A.mdisc_comp_perm (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (A ∘ σ) = mdisc A := by sorry
