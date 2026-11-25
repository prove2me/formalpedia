-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_embG_exp
-- name    : PI.UnitaryGroupMassFormula.UsCost.embG_exp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:46.718924+00:00
-- url     : https://prove2.me/theorems/0b6a4b2f-b048-405b-b762-7600be52ea9d
-- title:
--   Us Cost: emb G exp
-- statement:
--   The Us Cost construction uses the emb G exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L39-L43

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

theorem PI.UnitaryGroupMassFormula.UsCost.embG_exp (Y : B.Mat k ρ) :
    embG k j ρ (NormedSpace.exp Y) = NormedSpace.exp (blk3 0 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) := by sorry
