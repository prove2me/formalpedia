-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Lc_locally_compact_adelic_unitary
-- name    : PI.VolSemiDirect.W.Lc.locally_compact_adelic_unitary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:53:49.95979+00:00
-- url     : https://prove2.me/theorems/5cd21e53-5b53-518a-b5e7-ceae1d03284b
-- title:
--   Lc: locally compact adelic unitary
-- statement:
--   The Lc construction uses the locally compact adelic unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/LocallyCompactAdelicUnitary.lean#L9-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/LocallyCompactAdelicUnitary.lean#L9-L9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LcscHAOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Lc

theorem PI.VolSemiDirect.W.Lc.locally_compact_adelic_unitary : LcscHA := by sorry
