-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_append
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dwl_append
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:16.942604+00:00
-- url     : https://prove2.me/theorems/76ce31b3-a7c2-455f-849a-36afb494c767
-- title:
--   Unitary Corollary Derivatives: c A Dwl append
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dwl append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L66-L68

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

theorem PI.UnitaryCorollaryDerivatives.cA_Dwl_append (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r)
    (F : B.Mat k r → E) : Dwl lam (w ++ [x]) F = Dwl lam w (fun g => Dx x F g + lam x • F g) := by sorry
