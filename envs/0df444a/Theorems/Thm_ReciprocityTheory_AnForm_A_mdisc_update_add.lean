-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_add
-- name    : ReciprocityTheory.AnForm.A.mdisc_update_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:03.945191+00:00
-- url     : https://prove2.me/theorems/8879c678-d07a-44dc-9faa-389fa243f28d
-- title:
--   A: mdisc update add
-- statement:
--   The A construction uses the mdisc update add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean#L110-L115

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

theorem ReciprocityTheory.AnForm.A.mdisc_update_add (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A k (B + C)) =
      mdisc (Function.update A k B) + mdisc (Function.update A k C) := by sorry
