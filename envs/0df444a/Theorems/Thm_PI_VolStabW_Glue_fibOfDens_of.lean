-- Prove2me | Theorems.Thm_PI_VolStabW_Glue_fibOfDens_of
-- name    : PI.VolStabW.Glue.fibOfDens_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:13.043007+00:00
-- url     : https://prove2.me/theorems/113e13f8-4373-4eff-9e20-cd6272cde365
-- title:
--   Glue: fib Of Dens of
-- statement:
--   The Glue construction uses the fib Of Dens of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibGlue.lean#L280-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibGlue.lean#L280-L300

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.Glue
open MeasureTheory Topology Set Filter PI.VolStabW
open scoped CompactlySupported

theorem PI.VolStabW.Glue.fibOfDens_of (hDis : DisintStep) : FibOfDens := by sorry
