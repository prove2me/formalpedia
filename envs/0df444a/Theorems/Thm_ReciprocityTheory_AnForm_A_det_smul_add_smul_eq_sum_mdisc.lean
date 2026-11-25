-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_smul_add_smul_eq_sum_mdisc
-- name    : ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:05.611565+00:00
-- url     : https://prove2.me/theorems/12d16b40-03fb-42eb-92ed-3e0547d1ef8e
-- title:
--   A: det smul add smul eq sum mdisc
-- statement:
--   The A construction uses the det smul add smul eq sum mdisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L174-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L174-L200

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

theorem ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc (s t : ℂ) (A B : Matrix (Fin D) (Fin D) ℂ) :
    (s • A + t • B).det =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℂ) * s ^ i * t ^ (D - i) *
        mdisc (fun k : Fin D => if (k : ℕ) < i then A else B) := by sorry
