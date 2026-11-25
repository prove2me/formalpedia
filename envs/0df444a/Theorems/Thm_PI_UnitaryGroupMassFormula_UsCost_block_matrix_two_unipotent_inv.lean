-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_block_matrix_two_unipotent_inv
-- name    : PI.UnitaryGroupMassFormula.UsCost.block_matrix_two_unipotent_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:47.092967+00:00
-- url     : https://prove2.me/theorems/a27d224e-4ea9-576d-982d-a8d9b1fe6ca7
-- title:
--   Us Cost: block matrix two unipotent inv
-- statement:
--   The Us Cost construction uses the block matrix two unipotent inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Letters.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Letters.lean#L80-L84

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

theorem PI.UnitaryGroupMassFormula.UsCost.block_matrix_two_unipotent_inv {p s : ℕ} (b : Matrix (Fin p) (Fin s) ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) b 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ = blk2 1 (-b) 0 1 := by sorry
