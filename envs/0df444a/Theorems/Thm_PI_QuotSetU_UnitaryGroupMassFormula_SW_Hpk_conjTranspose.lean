-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_conjTranspose
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:20.847733+00:00
-- url     : https://prove2.me/theorems/f53b55f8-6f7c-46e6-beab-049efb3f02dc
-- title:
--   SW: Hpk conj Transpose
-- statement:
--   The SW construction uses the Hpk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L72-L79

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by sorry
