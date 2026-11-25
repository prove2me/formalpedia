-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_piW_algebraMap
-- name    : PI.VolStabSW.FiniteThetaCoordinates.norm_piW_algebraMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:18.545244+00:00
-- url     : https://prove2.me/theorems/2783ef47-0e15-48af-be8c-a171ee9d6e95
-- title:
--   Finite Theta Coordinates: norm pi W algebra Map
-- statement:
--   The Finite Theta Coordinates construction uses the norm pi W algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L162-L164

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabSW.FiniteThetaCoordinates.norm_piW_algebraMap (w : InfinitePlace F) (x : F) : ‖piW F w (algebraMap F (AF F) x)‖ = w x := by sorry
