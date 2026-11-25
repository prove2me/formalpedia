-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_conj_letter
-- name    : PI.UnitaryGroupMassFormula.UsCost.conj_letter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:35.846129+00:00
-- url     : https://prove2.me/theorems/f9e238a2-bbd3-4b38-9fe5-a5b4c669765c
-- title:
--   Us Cost: conj letter
-- statement:
--   The Us Cost construction uses the conj letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L65-L69

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

theorem PI.UnitaryGroupMassFormula.UsCost.conj_letter (x : RC k j ρ) (Y : B.Mat k ρ) (c : ℂ) :
    (Rn k j ρ x)⁻¹ * embG k j ρ (NormedSpace.exp (c • Y)) * Rn k j ρ x =
      NormedSpace.exp (c • cj k j ρ x Y) := by sorry
