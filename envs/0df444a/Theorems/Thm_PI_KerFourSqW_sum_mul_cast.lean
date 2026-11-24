-- Prove2me | Theorems.Thm_PI_KerFourSqW_sum_mul_cast
-- name    : PI.KerFourSqW.sum_mul_cast
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:58.295365+00:00
-- url     : https://prove2.me/theorems/a6779e0b-6553-495b-b2b0-957d37ff1c90
-- title:
--   Ker Four Sq W: sum mul cast
-- statement:
--   The Ker Four Sq W construction uses the sum mul cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L40-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW

theorem PI.KerFourSqW.sum_mul_cast {L : Type*} [Field L] [CharZero L] (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (j k : Fin 4) :
    ∑ b, (Q b j : L) * (Q b k : L) = if j = k then (a : L) else 0 := by sorry
