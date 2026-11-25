-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_nsmul
-- name    : PI.FinOrdRedOne.Core.pdvd_nsmul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:32.303104+00:00
-- url     : https://prove2.me/theorems/92dc3e5a-d0d6-4c5d-a315-bc1c2ca3ddfd
-- title:
--   Core: pdvd nsmul
-- statement:
--   The Core construction uses the pdvd nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L37-L40

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

theorem PI.FinOrdRedOne.Core.pdvd_nsmul {q : R} {k : ℕ} {A : Matrix n n R} (c : ℕ) (hA : PDvd q k A) :
    PDvd q k (c • A) := by sorry
