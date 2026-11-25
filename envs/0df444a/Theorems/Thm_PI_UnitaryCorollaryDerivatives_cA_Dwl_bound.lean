-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_bound
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dwl_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:35.231032+00:00
-- url     : https://prove2.me/theorems/3152df20-5069-4ce1-9571-22bc8c265af0
-- title:
--   Unitary Corollary Derivatives: c A Dwl bound
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dwl bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L70-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L70-L95

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

theorem PI.UnitaryCorollaryDerivatives.cA_Dwl_bound (lam : Bool × B.Mat k r → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (g : B.Mat k r) (M : ℝ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ‖lam x‖ ≤ Λ) → (∀ s : List (Bool × B.Mat k r), s.Sublist w → ‖Dw s F g‖ ≤ M) →
      ‖Dwl lam w F g‖ ≤ (1 + Λ) ^ w.length * M := by sorry
