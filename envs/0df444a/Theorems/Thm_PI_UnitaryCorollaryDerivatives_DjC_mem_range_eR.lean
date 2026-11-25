-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_mem_range_eR
-- name    : PI.UnitaryCorollaryDerivatives.DjC.mem_range_eR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:45.460171+00:00
-- url     : https://prove2.me/theorems/9084a4d0-2b03-4666-a92a-6eb6cff62d88
-- title:
--   Dj C: mem range e R
-- statement:
--   The Dj C construction uses the mem range e R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L112-L117

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

theorem PI.UnitaryCorollaryDerivatives.DjC.mem_range_eR (c : Fin (2 * (j + ρ) + k + 1)) : c ∈ Set.range (eR k j ρ) ↔ c.val < j := by sorry
