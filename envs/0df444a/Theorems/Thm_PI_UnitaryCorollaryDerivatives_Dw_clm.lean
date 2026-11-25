-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_Dw_clm
-- name    : PI.UnitaryCorollaryDerivatives.Dw_clm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:38.569347+00:00
-- url     : https://prove2.me/theorems/59f49423-606a-5030-a82a-0b05c4e92441
-- title:
--   Unitary Corollary Derivatives: Dw clm
-- statement:
--   The Unitary Corollary Derivatives construction uses the Dw clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L17-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem PI.UnitaryCorollaryDerivatives.Dw_clm {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (L : E →L[ℂ] E') (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun h => L (f h)) g = L (Dw w f g) := by sorry
