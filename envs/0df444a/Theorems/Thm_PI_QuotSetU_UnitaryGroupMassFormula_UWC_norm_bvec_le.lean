-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_bvec_le
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_bvec_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:49.637477+00:00
-- url     : https://prove2.me/theorems/fb143622-7b88-4c30-859e-9d7ff08f076e
-- title:
--   UWC: norm bvec le
-- statement:
--   The UWC construction uses the norm bvec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L74-L75

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_bvec_le (j i : Fin (2 * r + k + 1)) : ‖bvec j i‖ ≤ 1 := by sorry
