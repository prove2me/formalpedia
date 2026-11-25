-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pm_comp_bijective
-- name    : ReciprocityTheory.AnForm.A.pm_comp_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:19.292796+00:00
-- url     : https://prove2.me/theorems/65d62c84-0cde-440c-86f0-135fe8a80612
-- title:
--   A: pm comp bijective
-- statement:
--   The A construction uses the pm comp bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L79-L82

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

theorem ReciprocityTheory.AnForm.A.pm_comp_bijective (τ : Equiv.Perm (Fin D)) :
    Function.Bijective (fun g : Fin D → Fin D × ι => g ∘ τ) := by sorry
