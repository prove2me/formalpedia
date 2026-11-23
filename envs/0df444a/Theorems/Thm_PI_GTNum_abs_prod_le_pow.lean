-- Prove2me | Theorems.Thm_PI_GTNum_abs_prod_le_pow
-- name    : PI.GTNum.abs_prod_le_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:36.889043+00:00
-- url     : https://prove2.me/theorems/28260952-c8e1-40ec-a227-214cfc946017
-- title:
--   GTNum: abs prod le pow
-- statement:
--   The GTNum construction uses the abs prod le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L31-L33

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

theorem PI.GTNum.abs_prod_le_pow {α : Type*} (s : Finset α) (f : α → ℤ) (B : ℤ) (h : ∀ x ∈ s, |f x| ≤ B) :
    |∏ x ∈ s, f x| ≤ B ^ s.card := by sorry
