-- Prove2me | Theorems.Thm_PI_FrameInd_finrank_Uperp_of_det
-- name    : PI.FrameInd.finrank_Uperp_of_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:48.9198+00:00
-- url     : https://prove2.me/theorems/e7f9bdde-98b6-53db-ab26-860605b501e8
-- title:
--   Frame Ind: finrank Uperp of det
-- statement:
--   The Frame Ind construction uses the finrank Uperp of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L64-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L64-L80

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

theorem PI.FrameInd.finrank_Uperp_of_det (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) :
    Module.finrank ℂ (Uperp k r z z' g) = k - 1 := by sorry
