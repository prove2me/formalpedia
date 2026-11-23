-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_sum_row
-- name    : ReciprocityTheory.AnForm.A.mdisc_sum_row
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:50.633848+00:00
-- url     : https://prove2.me/theorems/a035f11c-1918-4b82-a615-b0d45ae47d67
-- title:
--   A: mdisc sum row
-- statement:
--   The A construction uses the mdisc sum row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L231-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L231-L244

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.A.mdisc_sum_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (k : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ j a b, S j a b = S a j b) :
    ∑ j, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S j)) = 0 := by sorry
