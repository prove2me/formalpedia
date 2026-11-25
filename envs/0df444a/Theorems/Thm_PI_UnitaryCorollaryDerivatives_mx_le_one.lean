-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_mx_le_one
-- name    : PI.UnitaryCorollaryDerivatives.mx_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:37.459633+00:00
-- url     : https://prove2.me/theorems/e84de577-a73e-5074-9db4-285027f8ef33
-- title:
--   Unitary Corollary Derivatives: mx le one
-- statement:
--   The Unitary Corollary Derivatives construction uses the mx le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/MxLeOne.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/MxLeOne.lean#L17-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_MxLeOne
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem PI.UnitaryCorollaryDerivatives.mx_le_one {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by sorry
