-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:47.312845+00:00
-- url     : https://prove2.me/theorems/6f9fa31c-ef03-4a71-9df7-6085aad82544
-- title:
--   SW: Hpk apply
-- statement:
--   The SW construction uses the Hpk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L43-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by sorry
