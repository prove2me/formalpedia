-- Prove2me | Theorems.Thm_PI_GTNum_sum_range_le_tele
-- name    : PI.GTNum.sum_range_le_tele
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:28.271994+00:00
-- url     : https://prove2.me/theorems/4fc205fb-2851-4fdb-bb01-064e859ccb6c
-- title:
--   GTNum: sum range le tele
-- statement:
--   The GTNum construction uses the sum range le tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L7-L15

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

theorem PI.GTNum.sum_range_le_tele (n : ℕ) (a t : ℕ → ℤ) (h : ∀ i < n, a i ≤ t i - t (i + 1)) :
    ∑ i ∈ range n, a i ≤ t 0 - t n := by sorry
