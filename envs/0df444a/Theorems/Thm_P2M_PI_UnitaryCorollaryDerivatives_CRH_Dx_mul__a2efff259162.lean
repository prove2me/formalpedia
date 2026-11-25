-- Prove2me | Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162
-- name    : P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:01:33.893161+00:00
-- url     : https://prove2.me/theorems/663fdb04-f069-46a1-9a93-6a2e65b90759
-- title:
--   P2 M PI Unitary Corollary Derivatives CRH Dx mul  a2efff259162: P2 M PI Unitary Corollary Derivatives CRH Dx mul  a2efff259162
-- statement:
--   The P2 M PI Unitary Corollary Derivatives CRH Dx mul  a2efff259162 construction uses the P2 M PI Unitary Corollary Derivatives CRH Dx mul  a2efff259162 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L64-L70

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

theorem P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162 (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by sorry

alias «PI».«UnitaryCorollaryDerivatives».«CRH».«Dx_mul'» := P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162
