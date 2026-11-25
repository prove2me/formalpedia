-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_blockDiag3_smul_middle
-- name    : PI.UnitaryGroupMassFormula.UsCost.blockDiag3_smul_middle
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:41.693742+00:00
-- url     : https://prove2.me/theorems/9067423b-1907-59e9-96ca-7f890a9b6f62
-- title:
--   Us Cost: block Diag3 smul middle
-- statement:
--   The Us Cost construction uses the block Diag3 smul middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L45-L51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
variable {k j ρ : ℕ}

theorem PI.UnitaryGroupMassFormula.UsCost.blockDiag3_smul_middle (c : ℂ) (Y : B.Mat k ρ) :
    (blk3 0 0 0 0 (c • Y) 0 0 0 0 : B.Mat k (j + ρ)) = c • blk3 0 0 0 0 Y 0 0 0 0 := by sorry
