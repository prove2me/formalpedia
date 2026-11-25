-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_lin
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dx_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:51.510917+00:00
-- url     : https://prove2.me/theorems/ee99bd3f-9a49-53c5-8eda-9123875f002c
-- title:
--   Unitary Corollary Derivatives: c A Dx lin
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dx lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L35-L40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cA_Dx_lin (x : Bool × B.Mat k r) {F₁ F₂ : B.Mat k r → E} (h₁ : Differentiable ℝ F₁)
    (h₂ : Differentiable ℝ F₂) (c : ℂ) :
    Dx x (fun g => F₁ g + c • F₂ g) = fun g => Dx x F₁ g + c • Dx x F₂ g := by sorry
