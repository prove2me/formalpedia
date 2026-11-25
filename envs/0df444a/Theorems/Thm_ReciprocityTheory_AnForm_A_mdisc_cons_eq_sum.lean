-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum
-- name    : ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:01.139526+00:00
-- url     : https://prove2.me/theorems/3e22e915-8c5a-40cd-9251-71652d6b07b9
-- title:
--   A: mdisc cons eq sum
-- statement:
--   The A construction uses the mdisc cons eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L252-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by sorry
