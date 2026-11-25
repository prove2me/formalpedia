-- Prove2me | Theorems.Thm_PI_FrameInd_gramM_herm
-- name    : PI.FrameInd.gramM_herm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:12.492796+00:00
-- url     : https://prove2.me/theorems/674fc066-09b5-4295-983a-5ac6e137d825
-- title:
--   Frame Ind: gram M herm
-- statement:
--   The Frame Ind construction uses the gram M herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L29-L32

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

theorem PI.FrameInd.gramM_herm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g)ᴴ = gramM k r z z' g := by sorry
