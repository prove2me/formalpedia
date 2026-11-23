-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mixedCof_diag
-- name    : ReciprocityTheory.AnForm.A.mixedCof_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:15.014964+00:00
-- url     : https://prove2.me/theorems/d599528d-0c40-4ba0-ade6-5c9ae1d3e996
-- title:
--   A: mixed Cof diag
-- statement:
--   The A construction uses the mixed Cof diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L320-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L320-L323

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

theorem ReciprocityTheory.AnForm.A.mixedCof_diag (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mixedCof B j j = (1 / ((n + 1 : ℕ) : ℂ)) *
      mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by sorry
