-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_contDiffOn_inv
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:47.455618+00:00
-- url     : https://prove2.me/theorems/b4653274-7b5d-467e-9a3c-d5081cebff1f
-- title:
--   ZI: cont Diff On inv
-- statement:
--   The ZI construction uses the cont Diff On inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L105-L108

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

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_inv (n : ℕ) : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x : En s | IsUnit x} := by sorry
