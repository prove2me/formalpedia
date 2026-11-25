-- Prove2me | Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_add__06d740adb120
-- name    : P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_add__06d740adb120
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:38.783347+00:00
-- url     : https://prove2.me/theorems/24d228f1-4876-4612-b8b6-9741198bb59a
-- title:
--   P2 M PI Unitary Corollary Derivatives CRH Dx add  06d740adb120: P2 M PI Unitary Corollary Derivatives CRH Dx add  06d740adb120
-- statement:
--   The P2 M PI Unitary Corollary Derivatives CRH Dx add  06d740adb120 construction uses the P2 M PI Unitary Corollary Derivatives CRH Dx add  06d740adb120 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L50-L53

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

theorem P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_add__06d740adb120 (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by sorry

alias «PI».«UnitaryCorollaryDerivatives».«CRH».«Dx_add'» := P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_add__06d740adb120
