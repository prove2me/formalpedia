-- Prove2me | Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_add__f7aedbeca0a8
-- name    : P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_add__f7aedbeca0a8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:01.574912+00:00
-- url     : https://prove2.me/theorems/756bd16c-242a-4c14-9603-c94470856ffa
-- title:
--   P2 M PI Unitary Corollary Derivatives CCA Dx add  f7aedbeca0a8: P2 M PI Unitary Corollary Derivatives CCA Dx add  f7aedbeca0a8
-- statement:
--   The P2 M PI Unitary Corollary Derivatives CCA Dx add  f7aedbeca0a8 construction uses the P2 M PI Unitary Corollary Derivatives CCA Dx add  f7aedbeca0a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L49-L52

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

theorem P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_add__f7aedbeca0a8 (x : Bool × Mat k r) {f₁ f₂ : Mat k r → ℂ} (h₁ : Differentiable ℝ f₁)
    (h₂ : Differentiable ℝ f₂) : Dx x (fun g => f₁ g + f₂ g) = fun g => Dx x f₁ g + Dx x f₂ g := by sorry

alias «PI».«UnitaryCorollaryDerivatives».«CCA».«Dx_add'» := P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_add__f7aedbeca0a8
