-- Prove2me | Theorems.Thm_PI_VolStabSW_continuous_sgl
-- name    : PI.VolStabSW.continuous_sgl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:42:00.750789+00:00
-- url     : https://prove2.me/theorems/588ef5d9-6e1e-47fa-8830-335b6e51779f
-- title:
--   Vol Stab SW: continuous sgl
-- statement:
--   The Vol Stab SW construction uses the continuous sgl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensChLift.lean#L236-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensChLift.lean#L236-L237

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift
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
open PI PI.VolStabSW
open Classical

theorem PI.VolStabSW.continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) := by sorry
