-- Prove2me | Theorems.Thm_PI_GTNum_card_erase_Icc_min
-- name    : PI.GTNum.card_erase_Icc_min
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:55.654374+00:00
-- url     : https://prove2.me/theorems/c3825118-7dd7-4fbe-961b-f19814e67c9c
-- title:
--   GTNum: card erase Icc min
-- statement:
--   The GTNum construction uses the card erase Icc min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L17-L24

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

theorem PI.GTNum.card_erase_Icc_min (a b c x : ℤ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hx : x ∈ Icc a (min b (a + c))) :
    ((((Icc a (min b (a + c))).erase x).card : ℕ) : ℤ) = min (b - a) c := by sorry
