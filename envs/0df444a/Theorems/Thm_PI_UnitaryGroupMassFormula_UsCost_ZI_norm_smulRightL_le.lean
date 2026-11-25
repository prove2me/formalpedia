-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_norm_smulRightL_le
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.norm_smulRightL_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:49.390637+00:00
-- url     : https://prove2.me/theorems/86ffbf8d-c3cc-47c8-841d-9f0bd2201bf6
-- title:
--   ZI: norm smul Right L le
-- statement:
--   The ZI construction uses the norm smul Right L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean#L73-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
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
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.norm_smulRightL_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖ContinuousLinearMap.smulRightL ℝ V E‖ ≤ 1 := by sorry
