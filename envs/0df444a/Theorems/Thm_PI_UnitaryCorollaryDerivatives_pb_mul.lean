-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_mul
-- name    : PI.UnitaryCorollaryDerivatives.pb_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:47.91951+00:00
-- url     : https://prove2.me/theorems/fcc21dbb-6c6a-4c8e-bd36-2463164764f6
-- title:
--   Unitary Corollary Derivatives: pb mul
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L105-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L105-L139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
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

theorem PI.UnitaryCorollaryDerivatives.pb_mul {e₁ e₂ : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e₁ f) (hh : PG e₂ h) :
    PG (e₁ + e₂) (fun g => f g * h g) := by sorry
