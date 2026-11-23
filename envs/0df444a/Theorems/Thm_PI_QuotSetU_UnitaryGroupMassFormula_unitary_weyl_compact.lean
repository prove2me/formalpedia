-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_unitary_weyl_compact
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:58.493048+00:00
-- url     : https://prove2.me/theorems/e08d2cec-775d-4d03-98b2-4a5379a3dd93
-- title:
--   Unitary Group Mass Formula: unitary weyl compact
-- statement:
--   The Unitary Group Mass Formula construction uses the unitary weyl compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L202-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L202-L222

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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.UWC

theorem PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact : UWCompact := by sorry
