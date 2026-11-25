-- Prove2me | Theorems.Thm_PI_VolStabW_linDens_holds
-- name    : PI.VolStabW.linDens_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:44:48.160867+00:00
-- url     : https://prove2.me/theorems/e406b542-95de-4768-a78c-3c15cd65a1ab
-- title:
--   Vol Stab W: lin Dens holds
-- statement:
--   The Vol Stab W construction uses the lin Dens holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensInfLoc.lean#L40-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensInfLoc.lean#L40-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology

theorem PI.VolStabW.linDens_holds : LinDens := by sorry
