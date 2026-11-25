-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_alg
-- name    : PI.UnitaryCorollaryDerivatives.cB_alg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:40:58.717227+00:00
-- url     : https://prove2.me/theorems/841607f9-c779-449b-ae09-118a3f3e6e23
-- title:
--   Unitary Corollary Derivatives: c B alg
-- statement:
--   The Unitary Corollary Derivatives construction uses the c B alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L17-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
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
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryCorollaryDerivatives.cB_alg (a b : ℕ) (c D : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * c) * D)⁻¹ ^ a * (star (Complex.exp ((t : ℂ) * c) * D))⁻¹ ^ b =
      Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) * (D⁻¹ ^ a * (star D)⁻¹ ^ b) := by sorry
