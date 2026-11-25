-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_sGroup_of
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.sGroup_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:13.552286+00:00
-- url     : https://prove2.me/theorems/da9a0b3a-1c34-4012-b806-a53a2691ea7f
-- title:
--   SW: s Group of
-- statement:
--   The SW construction uses the s Group of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsClosedS.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsClosedS.lean#L102-L105

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.sGroup_of (hUW : UWCompact) : SsetGroup := by sorry
