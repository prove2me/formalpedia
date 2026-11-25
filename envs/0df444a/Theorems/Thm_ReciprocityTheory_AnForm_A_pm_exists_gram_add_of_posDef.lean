-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_exists_gram_add_of_posDef
-- name    : ReciprocityTheory.AnForm.A.pm_exists_gram_add_of_posDef
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:26.381342+00:00
-- url     : https://prove2.me/theorems/69ac8320-f492-4073-99a5-dd7875a77a43
-- title:
--   A: pm exists gram add of pos Def
-- statement:
--   The A construction uses the pm exists gram add of pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L149-L157

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
open scoped MatrixOrder

theorem ReciprocityTheory.AnForm.A.pm_exists_gram_add_of_posDef [Nonempty (Fin D)] {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosDef) : ∃ r : ℝ, 0 < r ∧ ∃ v : Fin D → Fin D → ℂ,
      ∀ a b, A a b = ∑ s, v s a * star (v s b) + if a = b then (r : ℂ) else 0 := by sorry
