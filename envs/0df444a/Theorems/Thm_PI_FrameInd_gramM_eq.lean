-- Prove2me | Theorems.Thm_PI_FrameInd_gramM_eq
-- name    : PI.FrameInd.gramM_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:18:11.726285+00:00
-- url     : https://prove2.me/theorems/ee6349ed-7718-45a5-a19b-5274148aad58
-- title:
--   Frame Ind: gram M eq
-- statement:
--   The Frame Ind construction uses the gram M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L18-L24

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

theorem PI.FrameInd.gramM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    gramM k r z z' g = (Vc k r z z' g)ᴴ * Hpk k r * Vc k r z z' g := by sorry
