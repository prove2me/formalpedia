-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_lin
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dwl_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:56.825322+00:00
-- url     : https://prove2.me/theorems/5e75798c-c465-54de-8dd8-3cd1a160c99d
-- title:
--   Unitary Corollary Derivatives: c A Dwl lin
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dwl lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L51-L64

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

theorem PI.UnitaryCorollaryDerivatives.cA_Dwl_lin (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F₁ F₂ : B.Mat k r → E}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁) (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂) (c : ℂ) :
    Dwl lam w (fun g => F₁ g + c • F₂ g) = fun g => Dwl lam w F₁ g + c • Dwl lam w F₂ g := by sorry
