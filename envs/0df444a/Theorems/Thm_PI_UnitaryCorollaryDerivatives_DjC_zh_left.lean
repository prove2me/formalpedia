-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_zh_left
-- name    : PI.UnitaryCorollaryDerivatives.DjC.zh_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:28.025854+00:00
-- url     : https://prove2.me/theorems/588bd4e5-cc1d-5f23-ac28-80ff1c982d18
-- title:
--   Dj C: zh left
-- statement:
--   The Dj C construction uses the zh left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L193-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L193-L208

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
variable {k j ρ}

theorem PI.UnitaryCorollaryDerivatives.DjC.zh_left (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eL k j ρ))ᶜ E) :
    Zh k j ρ (E * g) = sub (eL k j ρ) E * Zh k j ρ g := by sorry
