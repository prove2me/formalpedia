-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_inv_UH
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_inv_UH
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:42:36.180116+00:00
-- url     : https://prove2.me/theorems/0a4efae4-f0f0-4527-810a-82b964862515
-- title:
--   SW: inv inv UH
-- statement:
--   The SW construction uses the inv inv UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/NilpotentSubgroup.lean#L136-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/NilpotentSubgroup.lean#L136-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
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
variable {k r : ℕ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_inv_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r)) :
    a⁻¹⁻¹ = a := by sorry
