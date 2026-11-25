-- Prove2me | Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76
-- name    : P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:59:00.036653+00:00
-- url     : https://prove2.me/theorems/a70070b9-ad73-5673-ac50-a458a071b3f5
-- title:
--   P2 M PI Unitary Corollary Derivatives CRH Dw add  d7ab365c3e76: P2 M PI Unitary Corollary Derivatives CRH Dw add  d7ab365c3e76
-- statement:
--   The P2 M PI Unitary Corollary Derivatives CRH Dw add  d7ab365c3e76 construction uses the P2 M PI Unitary Corollary Derivatives CRH Dw add  d7ab365c3e76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L55-L62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76 (w : List (Bool × Mat k r)) {a b : Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by sorry

alias «PI».«UnitaryCorollaryDerivatives».«CRH».«Dw_add'» := P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76
