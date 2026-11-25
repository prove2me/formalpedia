-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_presR
-- name    : PI.UnitaryCorollaryDerivatives.DjC.presR
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:42.309017+00:00
-- url     : https://prove2.me/theorems/8280e1e1-26b9-4c32-9a0d-ad946616efab
-- title:
--   Dj C: pres R
-- statement:
--   The Dj C construction uses the pres R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L143-L146

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

theorem PI.UnitaryCorollaryDerivatives.DjC.presR {Y : B.Mat k (j + ρ)} (hY : inLieP k j ρ Y) : Pres (Set.range (eR k j ρ)) Y := by sorry
