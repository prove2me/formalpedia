-- Prove2me | Theorems.Thm_PI_FrameInd_Uperp_mat
-- name    : PI.FrameInd.Uperp_mat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:43.687931+00:00
-- url     : https://prove2.me/theorems/6b92fd1d-d78b-4164-a0e3-a050b11b706f
-- title:
--   Frame Ind: Uperp mat
-- statement:
--   The Frame Ind construction uses the Uperp mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L26-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd

theorem PI.FrameInd.Uperp_mat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Uperp k r z z' g = LinearMap.ker (Matrix.mulVecLin ((Vc k r z z' g)ᴴ * Hpk k r)) := by sorry
