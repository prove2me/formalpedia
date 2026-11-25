-- Prove2me | Theorems.Thm_PI_UnitKronW_eq_zero_of_mulVec
-- name    : PI.UnitKronW.eq_zero_of_mulVec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:39.798511+00:00
-- url     : https://prove2.me/theorems/2fe0b55c-4139-4569-833b-785c5f6bc2a0
-- title:
--   Unit Kron W: eq zero of mul Vec
-- statement:
--   The Unit Kron W construction uses the eq zero of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/EqZeroOfMulVec.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/EqZeroOfMulVec.lean#L18-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder

theorem PI.UnitKronW.eq_zero_of_mulVec {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (h : ∀ x, N *ᵥ x = 0) : N = 0 := by sorry
