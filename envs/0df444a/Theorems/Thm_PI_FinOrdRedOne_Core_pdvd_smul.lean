-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_smul
-- name    : PI.FinOrdRedOne.Core.pdvd_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:34.312816+00:00
-- url     : https://prove2.me/theorems/0300569d-ec9c-476e-8c5a-cc7c9644a9d5
-- title:
--   Core: pdvd smul
-- statement:
--   The Core construction uses the pdvd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L32-L35

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

theorem PI.FinOrdRedOne.Core.pdvd_smul {q : R} {k : ℕ} {A : Matrix n n R} (c : R) (hA : PDvd q k A) :
    PDvd q k (c • A) := by sorry
