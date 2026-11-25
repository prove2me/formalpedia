-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_zh_right
-- name    : PI.UnitaryCorollaryDerivatives.DjC.zh_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:32.830917+00:00
-- url     : https://prove2.me/theorems/53043505-8aff-5372-a430-5c747b595eb6
-- title:
--   Dj C: zh right
-- statement:
--   The Dj C construction uses the zh right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L176-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L176-L191

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

theorem PI.UnitaryCorollaryDerivatives.DjC.zh_right (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eR k j ρ)) E) :
    Zh k j ρ (g * E) = Zh k j ρ g * sub (eR k j ρ) E := by sorry
