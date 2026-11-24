-- Prove2me | Theorems.Thm_PI_FJMD_negPart_length
-- name    : PI.FJMD.negPart_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:51.595195+00:00
-- url     : https://prove2.me/theorems/4f47e131-69f2-47a0-8121-90287321eac3
-- title:
--   FJMD: neg Part length
-- statement:
--   The FJMD construction uses the neg Part length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L121-L122

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

theorem PI.FJMD.negPart_length (b : List ℤ) : (PI.FJM.negPart b).length = b.length := by sorry
