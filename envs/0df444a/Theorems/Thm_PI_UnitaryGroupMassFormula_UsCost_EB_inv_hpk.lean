-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_EB_inv_hpk
-- name    : PI.UnitaryGroupMassFormula.UsCost.EB_inv_hpk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:51:12.859065+00:00
-- url     : https://prove2.me/theorems/5f6f53c1-3241-47e9-bcae-30a6aad956f1
-- title:
--   Us Cost: EB inv hpk
-- statement:
--   The Us Cost construction uses the EB inv hpk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Letters.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Letters.lean#L16-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.EB_inv_hpk {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    EB n⁻¹ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * B.gN n) := by sorry
