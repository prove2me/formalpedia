-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_conj_exp
-- name    : PI.UnitaryGroupMassFormula.UsCost.conj_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:00.795292+00:00
-- url     : https://prove2.me/theorems/e26c7f02-ce36-5b16-b79e-b67b34307d73
-- title:
--   Us Cost: conj exp
-- statement:
--   The Us Cost construction uses the conj exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L53-L55

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

theorem PI.UnitaryGroupMassFormula.UsCost.conj_exp {m : ℕ} (n X : Matrix (Fin m) (Fin m) ℂ) (hn : n * n⁻¹ = 1) :
    n⁻¹ * NormedSpace.exp X * n = NormedSpace.exp (n⁻¹ * X * n) := by sorry
