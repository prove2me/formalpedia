-- Prove2me | Theorems.Thm_PI_VolStabSW_submLocal_of
-- name    : PI.VolStabSW.submLocal_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:38:19.712186+00:00
-- url     : https://prove2.me/theorems/d916ebb6-95d1-5ce7-a8e6-e38ee000ae5a
-- title:
--   Vol Stab SW: subm Local of
-- statement:
--   The Vol Stab SW construction uses the subm Local of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfLoc.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfLoc.lean#L25-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology

theorem PI.VolStabSW.submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by sorry
