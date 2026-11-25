-- Prove2me | Theorems.Thm_PI_FJM_cauchy_highest_weight
-- name    : PI.FJM.cauchy_highest_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:05.052811+00:00
-- url     : https://prove2.me/theorems/d6c3a1d7-c7d4-4599-8792-173dc119ca78
-- title:
--   FJM: cauchy highest weight
-- statement:
--   The FJM construction uses the cauchy highest weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauchyFin.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauchyFin.lean#L6-L7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHWOfShape
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauBFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJM

theorem PI.FJM.cauchy_highest_weight : CauchyHW := by sorry
