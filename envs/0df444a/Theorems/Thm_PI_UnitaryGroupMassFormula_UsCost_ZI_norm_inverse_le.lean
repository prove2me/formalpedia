-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_norm_inverse_le
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.norm_inverse_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:51.268939+00:00
-- url     : https://prove2.me/theorems/6750fdf5-8b78-49e8-b8ba-c92081082764
-- title:
--   ZI: norm inverse le
-- statement:
--   The ZI construction uses the norm inverse le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L110-L113

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.norm_inverse_le {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    ‖Ring.inverse (eA s Z)‖ ≤ ‖eA s‖ * ‖invF s Z‖ := by sorry
