-- Prove2me | Theorems.Thm_PI_VolStabW_discHF_holds
-- name    : PI.VolStabW.discHF_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:59.218339+00:00
-- url     : https://prove2.me/theorems/8e4c4af0-ea60-5260-b083-a56dc5e987e1
-- title:
--   Vol Stab W: disc HF holds
-- statement:
--   The Vol Stab W construction uses the disc HF holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExFDStabFin.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExFDStabFin.lean#L9-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStab
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoClose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExFDStabFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabW

theorem PI.VolStabW.discHF_holds : DiscHF := by sorry
