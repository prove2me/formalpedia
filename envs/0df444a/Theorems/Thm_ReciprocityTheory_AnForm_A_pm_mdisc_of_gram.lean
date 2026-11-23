-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_of_gram
-- name    : ReciprocityTheory.AnForm.A.pm_mdisc_of_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:43.46828+00:00
-- url     : https://prove2.me/theorems/3cf0a563-8af3-463d-b5fc-d3addddde366
-- title:
--   A: pm mdisc of gram
-- statement:
--   The A construction uses the pm mdisc of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L159-L164

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

theorem ReciprocityTheory.AnForm.A.pm_mdisc_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ι → Fin D → ℂ)
    (h : ∀ k a b, A k a b = ∑ r, w k r a * star (w k r b)) :
    mdisc A = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by sorry
