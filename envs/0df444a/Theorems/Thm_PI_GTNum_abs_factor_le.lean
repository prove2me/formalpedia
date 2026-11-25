-- Prove2me | Theorems.Thm_PI_GTNum_abs_factor_le
-- name    : PI.GTNum.abs_factor_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:55.300798+00:00
-- url     : https://prove2.me/theorems/385416f9-3ae3-4b5b-8dd3-6f0afd3ebb58
-- title:
--   GTNum: abs factor le
-- statement:
--   The GTNum construction uses the abs factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L39-L44

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

theorem PI.GTNum.abs_factor_le (v s L S : ℤ) (i j n : ℕ) (hi : i < n) (hj : j < n)
    (hv1 : L ≤ v) (hv2 : v ≤ S + (S - L)) (hs1 : L ≤ s) (hs2 : s ≤ S) :
    |v - (i : ℤ) - s + (j : ℤ)| ≤ 2 * (S - L) + ((n + 1 : ℕ) : ℤ) := by sorry
