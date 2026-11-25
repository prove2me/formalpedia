-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_mem_range_eL
-- name    : PI.UnitaryCorollaryDerivatives.DjC.mem_range_eL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:30.359559+00:00
-- url     : https://prove2.me/theorems/752d6434-68c4-465a-9cfd-e18e3aa13c43
-- title:
--   Dj C: mem range e L
-- statement:
--   The Dj C construction uses the mem range e L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean#L119-L131

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

theorem PI.UnitaryCorollaryDerivatives.DjC.mem_range_eL (c : Fin (2 * (j + ρ) + k + 1)) :
    c ∈ Set.range (eL k j ρ) ↔ 2 * (j + ρ) + k + 1 ≤ c.val + j := by sorry
