-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_pow_smul
-- name    : PI.FinOrdRedOne.Core.pdvd_pow_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:36.040236+00:00
-- url     : https://prove2.me/theorems/39ea29aa-91f5-43ff-9a85-40adc2af7c70
-- title:
--   Core: pdvd pow smul
-- statement:
--   The Core construction uses the pdvd pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L46-L48

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

theorem PI.FinOrdRedOne.Core.pdvd_pow_smul (q : R) (a m : ℕ) (X : Matrix n n R) :
    PDvd q (a * m) ((q ^ a • X) ^ m) := by sorry
