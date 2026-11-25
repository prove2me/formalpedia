-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_Dw_mulL
-- name    : PI.UnitaryCorollaryDerivatives.pb_Dw_mulL
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:58.380499+00:00
-- url     : https://prove2.me/theorems/b401166a-b968-5eab-97fc-935e6977b62f
-- title:
--   Unitary Corollary Derivatives: pb Dw mul L
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb Dw mul L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L86-L103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.pb_Dw_mulL {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → ℂ}
    (hf : B.CkOn w.length (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) g =
      ContinuousLinearMap.mul ℂ ℂ (Dw w f g) := by sorry
