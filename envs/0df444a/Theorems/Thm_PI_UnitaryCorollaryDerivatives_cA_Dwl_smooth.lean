-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_smooth
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dwl_smooth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:32.72841+00:00
-- url     : https://prove2.me/theorems/5bf762da-beff-41ba-bee3-2b11e7886793
-- title:
--   Unitary Corollary Derivatives: c A Dwl smooth
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dwl smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L45-L49

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

theorem PI.UnitaryCorollaryDerivatives.cA_Dwl_smooth (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dwl lam w F) := by sorry
