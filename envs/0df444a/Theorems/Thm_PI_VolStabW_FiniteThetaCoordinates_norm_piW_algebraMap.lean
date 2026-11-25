-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_norm_piW_algebraMap
-- name    : PI.VolStabW.FiniteThetaCoordinates.norm_piW_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:42:55.185858+00:00
-- url     : https://prove2.me/theorems/dd110aee-d96b-4198-a1d8-8aebd624672f
-- title:
--   Finite Theta Coordinates: norm pi W algebra Map
-- statement:
--   The Finite Theta Coordinates construction uses the norm pi W algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L162-L164

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabW.FiniteThetaCoordinates.norm_piW_algebraMap (w : InfinitePlace F) (x : F) : ‖piW F w (algebraMap F (AF F) x)‖ = w x := by sorry
