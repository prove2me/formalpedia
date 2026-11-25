-- Prove2me | Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764
-- name    : P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:18:18.789813+00:00
-- url     : https://prove2.me/theorems/aa187f24-2f50-40cf-b106-e02421447f5f
-- title:
--   P2 M PI Unitary Corollary Derivatives CCA Dw add  1dc732627764: P2 M PI Unitary Corollary Derivatives CCA Dw add  1dc732627764
-- statement:
--   The P2 M PI Unitary Corollary Derivatives CCA Dw add  1dc732627764 construction uses the P2 M PI Unitary Corollary Derivatives CCA Dw add  1dc732627764 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L54-L61

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

theorem P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764 (w : List (Bool × Mat k r)) {f₁ f₂ : Mat k r → ℂ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) : Dw w (fun g => f₁ g + f₂ g) = fun g => Dw w f₁ g + Dw w f₂ g := by sorry

alias «PI».«UnitaryCorollaryDerivatives».«CCA».«Dw_add'» := P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764
