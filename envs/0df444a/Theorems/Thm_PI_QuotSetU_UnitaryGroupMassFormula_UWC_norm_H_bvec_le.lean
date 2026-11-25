-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_H_bvec_le
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_H_bvec_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:30.413614+00:00
-- url     : https://prove2.me/theorems/c99afccd-1a70-4f2e-8287-f502a37f2e3f
-- title:
--   UWC: norm H bvec le
-- statement:
--   The UWC construction uses the norm H bvec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean#L77-L79

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_H_bvec_le (j i : Fin (2 * r + k + 1)) : ‖(Hpk k r *ᵥ bvec j) i‖ ≤ 1 := by sorry
