-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_dirL_le
-- name    : PI.UnitaryCorollaryDerivatives.pb_dirL_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:43.691718+00:00
-- url     : https://prove2.me/theorems/bc70d67a-db3f-5e6f-acb0-0f30eb769c0d
-- title:
--   Unitary Corollary Derivatives: pb dir L le
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb dir L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L46-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L46-L60

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

theorem PI.UnitaryCorollaryDerivatives.pb_dirL_le {x : Bool × B.Mat k r} (hx : B.unitLie k r x.2) (g : B.Mat k r) :
    ‖dirL x g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by sorry
