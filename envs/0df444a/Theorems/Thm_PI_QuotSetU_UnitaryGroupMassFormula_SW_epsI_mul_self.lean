-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_mul_self
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:08.315796+00:00
-- url     : https://prove2.me/theorems/bf719539-9441-5ed6-b3ed-b1740483616e
-- title:
--   SW: eps I mul self
-- statement:
--   The SW construction uses the eps I mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L35-L37

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by sorry
