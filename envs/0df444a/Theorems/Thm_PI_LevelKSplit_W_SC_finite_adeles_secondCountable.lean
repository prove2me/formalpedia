-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SC_finite_adeles_secondCountable
-- name    : PI.LevelKSplit.W.SC.finite_adeles_secondCountable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:17.713296+00:00
-- url     : https://prove2.me/theorems/81c6f321-5605-465a-9f4e-04bd25583186
-- title:
--   SC: finite adeles second Countable
-- statement:
--   The SC construction uses the finite adeles second Countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/FiniteAdelesSecondCountable.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/FiniteAdelesSecondCountable.lean#L7-L8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SC

theorem PI.LevelKSplit.W.SC.finite_adeles_secondCountable : PI.LevelKSplit.W.ExS.SCAf := by sorry
