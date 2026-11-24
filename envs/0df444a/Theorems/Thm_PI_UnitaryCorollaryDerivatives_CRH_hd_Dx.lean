-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_hd_Dx
-- name    : PI.UnitaryCorollaryDerivatives.CRH.hd_Dx
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:37.684605+00:00
-- url     : https://prove2.me/theorems/b29076ea-575f-41b7-9bae-70558d6ac106
-- title:
--   CRH: hd Dx
-- statement:
--   The CRH construction uses the hd Dx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRA.lean#L24-L27

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

theorem PI.UnitaryCorollaryDerivatives.CRH.hd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by sorry
