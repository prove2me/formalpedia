-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_smul_cancel
-- name    : PI.FinOrdRedOne.Core.smul_cancel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:28.912976+00:00
-- url     : https://prove2.me/theorems/c41e40a4-fa05-4f00-bc2a-9ad1a39563fb
-- title:
--   Core: smul cancel
-- statement:
--   The Core construction uses the smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L58-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem PI.FinOrdRedOne.Core.smul_cancel [IsDomain R] {c : R} (hc : c ≠ 0) {X Y : Matrix n n R} (h : c • X = c • Y) :
    X = Y := by sorry
