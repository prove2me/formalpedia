-- Prove2me | Theorems.Thm_PI_VolStabS_sum_sgl
-- name    : PI.VolStabS.sum_sgl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:42.463022+00:00
-- url     : https://prove2.me/theorems/694658a5-ecd9-48fb-bc34-a09fe32947d0
-- title:
--   Vol Stab S: sum sgl
-- statement:
--   The Vol Stab S construction uses the sum sgl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensChLift.lean#L143-L145

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

theorem PI.VolStabS.sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by sorry
