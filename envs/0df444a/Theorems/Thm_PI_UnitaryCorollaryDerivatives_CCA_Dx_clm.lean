-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_Dx_clm
-- name    : PI.UnitaryCorollaryDerivatives.CCA.Dx_clm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:54.85659+00:00
-- url     : https://prove2.me/theorems/98341727-8c7f-4473-93d0-d30398de13e2
-- title:
--   CCA: Dx clm
-- statement:
--   The CCA construction uses the Dx clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L71-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CCA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.CCA.Dx_clm (x : Bool × Mat k r) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by sorry
