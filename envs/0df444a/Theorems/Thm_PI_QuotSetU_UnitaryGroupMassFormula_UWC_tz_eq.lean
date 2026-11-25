-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_tz_eq
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.tz_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:23.322408+00:00
-- url     : https://prove2.me/theorems/e2a1d7fa-0927-4fe4-a872-8ac1631850bd
-- title:
--   UWC: tz eq
-- statement:
--   The UWC construction uses the tz eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L55-L62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.tz_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    Tz k r z = ‖z (lI k r)‖ ^ 2 - ∑ i ∈ Wp k r, ‖z i‖ ^ 2 := by sorry
