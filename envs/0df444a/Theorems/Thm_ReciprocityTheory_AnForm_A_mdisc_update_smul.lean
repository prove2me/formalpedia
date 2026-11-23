-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul
-- name    : ReciprocityTheory.AnForm.A.mdisc_update_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:22.342781+00:00
-- url     : https://prove2.me/theorems/1eb0fbf0-76d3-45c2-bc17-d7bd152511b4
-- title:
--   A: mdisc update smul
-- statement:
--   The A construction uses the mdisc update smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L117-L121

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

theorem ReciprocityTheory.AnForm.A.mdisc_update_smul (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D) (c : ℂ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A k (c • B)) = c * mdisc (Function.update A k B) := by sorry
