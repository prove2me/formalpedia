-- Prove2me | Theorems.Thm_PI_FJMD_posPart_length
-- name    : PI.FJMD.posPart_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:55.869845+00:00
-- url     : https://prove2.me/theorems/2e64de1b-61fb-41a1-be78-ef3142366227
-- title:
--   FJMD: pos Part length
-- statement:
--   The FJMD construction uses the pos Part length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L118-L119

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM

theorem PI.FJMD.posPart_length (a : List ℤ) : (PI.FJM.posPart a).length = a.length := by sorry
