-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm
-- name    : ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:57.372348+00:00
-- url     : https://prove2.me/theorems/218e86db-767b-48cc-9dca-baf11e1e2ab8
-- title:
--   A: mdisc eq sum perm
-- statement:
--   The A construction uses the mdisc eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L55-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L55-L82

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

theorem ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ σ : Equiv.Perm (Fin D), (Matrix.of fun i j => A (σ j) i j).det := by sorry
