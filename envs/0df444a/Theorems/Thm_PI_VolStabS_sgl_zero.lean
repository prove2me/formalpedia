-- Prove2me | Theorems.Thm_PI_VolStabS_sgl_zero
-- name    : PI.VolStabS.sgl_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:23.882317+00:00
-- url     : https://prove2.me/theorems/d85702f4-aaa7-586e-bcfb-eebcba8383bf
-- title:
--   Vol Stab S: sgl zero
-- statement:
--   The Vol Stab S construction uses the sgl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L135-L136

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

theorem PI.VolStabS.sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 := by sorry
