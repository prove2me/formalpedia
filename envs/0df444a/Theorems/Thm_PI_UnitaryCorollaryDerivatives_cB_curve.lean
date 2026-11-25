-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_curve
-- name    : PI.UnitaryCorollaryDerivatives.cB_curve
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:08.475533+00:00
-- url     : https://prove2.me/theorems/2bcdbf91-53b6-56bc-9113-0f097609faea
-- title:
--   Unitary Corollary Derivatives: c B curve
-- statement:
--   The Unitary Corollary Derivatives construction uses the c B curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L39-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L39-L60

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

theorem PI.UnitaryCorollaryDerivatives.cB_curve (hC : DjCurve) (k j ρ a b : ℕ) :
    ∃ lam : Bool × B.Mat k (j + ρ) → ℂ, ∀ x : Bool × B.Mat k (j + ρ), inLieP k j ρ x.2 →
      ‖lam x‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * lam x) * hhF k j ρ a b g := by sorry
