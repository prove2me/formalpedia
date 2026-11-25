-- Prove2me | Theorems.Thm_PI_VolStabW_DiscreteGroups_fibOfDens_holds
-- name    : PI.VolStabW.DiscreteGroups.fibOfDens_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:42:23.55803+00:00
-- url     : https://prove2.me/theorems/52bdb4db-d72d-4b30-a5dc-bb3048195674
-- title:
--   Discrete Groups: fib Of Dens holds
-- statement:
--   The Discrete Groups construction uses the fib Of Dens holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibDis.lean#L223-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibDis.lean#L223-L223

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal

theorem PI.VolStabW.DiscreteGroups.fibOfDens_holds : FibOfDens := by sorry
