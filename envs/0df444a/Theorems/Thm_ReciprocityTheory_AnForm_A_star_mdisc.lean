-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_star_mdisc
-- name    : ReciprocityTheory.AnForm.A.star_mdisc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:29.507703+00:00
-- url     : https://prove2.me/theorems/c865df61-029e-4345-8b94-d8487cedf425
-- title:
--   A: star mdisc
-- statement:
--   The A construction uses the star mdisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L202-L205

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

theorem ReciprocityTheory.AnForm.A.star_mdisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    star (mdisc A) = mdisc (fun k => (A k)ᴴ) := by sorry
