-- Prove2me | Theorems.Thm_PI_KerFourSqW_quatMat_transpose_mul
-- name    : PI.KerFourSqW.quatMat_transpose_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:55.570932+00:00
-- url     : https://prove2.me/theorems/ea078443-6d6c-57c0-95d6-13ff564e90da
-- title:
--   Ker Four Sq W: quat Mat transpose mul
-- statement:
--   The Ker Four Sq W construction uses the quat Mat transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L14-L18

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

theorem PI.KerFourSqW.quatMat_transpose_mul (r₁ r₂ r₃ r₄ : ℚ) :
    (quatMat r₁ r₂ r₃ r₄)ᵀ * quatMat r₁ r₂ r₃ r₄ = (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by sorry
