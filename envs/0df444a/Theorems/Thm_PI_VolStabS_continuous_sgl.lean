-- Prove2me | Theorems.Thm_PI_VolStabS_continuous_sgl
-- name    : PI.VolStabS.continuous_sgl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:31.123484+00:00
-- url     : https://prove2.me/theorems/c0a0ffd2-8a7b-4b69-b2a3-6dc2b1e58a73
-- title:
--   Vol Stab S: continuous sgl
-- statement:
--   The Vol Stab S construction uses the continuous sgl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L139-L140

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensChLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabS
open Classical

theorem PI.VolStabS.continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) := by sorry
