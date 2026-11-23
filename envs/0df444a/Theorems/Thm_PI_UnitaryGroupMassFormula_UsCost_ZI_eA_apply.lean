-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_eA_apply
-- name    : PI.UnitaryGroupMassFormula.UsCost.ZI.eA_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:13.590243+00:00
-- url     : https://prove2.me/theorems/eced2caf-8e69-4072-a337-280dbec8e019
-- title:
--   ZI: e A apply
-- statement:
--   The ZI construction uses the e A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean#L33-L33

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

theorem PI.UnitaryGroupMassFormula.UsCost.ZI.eA_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : eA s Z v = (Matrix.of Z).mulVec v := by sorry
