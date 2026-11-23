-- Prove2me | Theorems.Thm_PI_GTNum_abs_prod_le_prod
-- name    : PI.GTNum.abs_prod_le_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:57.727955+00:00
-- url     : https://prove2.me/theorems/e119963e-b40b-40d6-aa66-674c1d98016c
-- title:
--   GTNum: abs prod le prod
-- statement:
--   The GTNum construction uses the abs prod le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L26-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GTNum
open Finset

theorem PI.GTNum.abs_prod_le_prod {α : Type*} (s : Finset α) (f b : α → ℤ) (h : ∀ x ∈ s, |f x| ≤ b x) :
    |∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by sorry
