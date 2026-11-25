-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_mul_norm_le
-- name    : PI.UnitaryCorollaryDerivatives.pb_mul_norm_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:30.279596+00:00
-- url     : https://prove2.me/theorems/f2720c2d-52f9-5d0f-a962-7f343fa50aac
-- title:
--   Unitary Corollary Derivatives: pb mul norm le
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb mul norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L35-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.pb_mul_norm_le (A A' : B.Mat k r) : ‖A * A'‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖A‖ * ‖A'‖) := by sorry
