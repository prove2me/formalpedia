-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_hasDeriv
-- name    : PI.UnitaryCorollaryDerivatives.cA_hasDeriv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:38.737088+00:00
-- url     : https://prove2.me/theorems/c7a377e6-9c12-4106-b290-96bcbe5cf782
-- title:
--   Unitary Corollary Derivatives: c A has Deriv
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L20-L22

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

theorem PI.UnitaryCorollaryDerivatives.cA_hasDeriv (x : Bool × B.Mat k r) {F : B.Mat k r → E} {g : B.Mat k r} (hd : DifferentiableAt ℝ F g) :
    HasDerivAt (fun t : ℝ => F (crv x g t)) (fderiv ℝ F g (dirv x g)) 0 := by sorry
