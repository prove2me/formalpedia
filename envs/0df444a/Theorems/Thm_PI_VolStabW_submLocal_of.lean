-- Prove2me | Theorems.Thm_PI_VolStabW_submLocal_of
-- name    : PI.VolStabW.submLocal_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:21.383635+00:00
-- url     : https://prove2.me/theorems/e0156fe0-097c-4fc7-89f9-80c6ffdeb3c1
-- title:
--   Vol Stab W: subm Local of
-- statement:
--   The Vol Stab W construction uses the subm Local of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensInfLoc.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensInfLoc.lean#L25-L34

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

theorem PI.VolStabW.submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by sorry
