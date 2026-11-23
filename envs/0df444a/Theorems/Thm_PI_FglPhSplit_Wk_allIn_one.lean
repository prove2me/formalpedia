-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_allIn_one
-- name    : PI.FglPhSplit.Wk.allIn_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:47.570646+00:00
-- url     : https://prove2.me/theorems/11dba49a-f73b-4b9a-a0a0-5884d2438a2c
-- title:
--   Wk: all In one
-- statement:
--   The Wk construction uses the all In one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L22-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]

theorem PI.FglPhSplit.Wk.allIn_one {W : Subring K} {σ : Type} : AllIn W (1 : MvPowerSeries σ K) := by sorry
