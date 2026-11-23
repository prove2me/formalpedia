-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_isOpen_det
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.isOpen_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:06.179478+00:00
-- url     : https://prove2.me/theorems/3c9d06ee-4fda-4fe8-a7fb-3a04ee84a8fc
-- title:
--   ZI: is Open det
-- statement:
--   The ZI construction uses the is Open det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L94-L95

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

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.isOpen_det : IsOpen {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by sorry
