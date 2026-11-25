-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_uw_entry_bound
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.uw_entry_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:09.110112+00:00
-- url     : https://prove2.me/theorems/5029558a-586d-5870-aeb9-97eead6e6843
-- title:
--   UWC: uw entry bound
-- statement:
--   The UWC construction uses the uw entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L86-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L86-L194

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.uw_entry_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) : ‖h i j‖ ≤ Bd k r z := by sorry
