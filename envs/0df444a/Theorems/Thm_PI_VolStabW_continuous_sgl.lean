-- Prove2me | Theorems.Thm_PI_VolStabW_continuous_sgl
-- name    : PI.VolStabW.continuous_sgl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:42:32.73585+00:00
-- url     : https://prove2.me/theorems/5bb6ad88-98ee-5184-bd33-cb6307a4b6da
-- title:
--   Vol Stab W: continuous sgl
-- statement:
--   The Vol Stab W construction uses the continuous sgl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensChLift.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensChLift.lean#L139-L140

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift
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
open PI PI.VolStabW
open Classical

theorem PI.VolStabW.continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) := by sorry
