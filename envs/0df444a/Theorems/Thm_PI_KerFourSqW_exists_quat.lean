-- Prove2me | Theorems.Thm_PI_KerFourSqW_exists_quat
-- name    : PI.KerFourSqW.exists_quat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:49.126124+00:00
-- url     : https://prove2.me/theorems/e3b7ead0-53f0-579a-bc53-8b910ef9c542
-- title:
--   Ker Four Sq W: exists quat
-- statement:
--   The Ker Four Sq W construction uses the exists quat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L35-L38

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

theorem PI.KerFourSqW.exists_quat (a : ℚ) (ha : 0 < a) :
    ∃ Q : Matrix (Fin 4) (Fin 4) ℚ, Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by sorry
