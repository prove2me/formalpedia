-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_continuous_piW_inf
-- name    : PI.VolStabW.FiniteThetaCoordinates.continuous_piW_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:30.900636+00:00
-- url     : https://prove2.me/theorems/742fde0f-dbea-4c0e-921e-e06bdda601c2
-- title:
--   Finite Theta Coordinates: continuous pi W inf
-- statement:
--   The Finite Theta Coordinates construction uses the continuous pi W inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L158-L160

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

theorem PI.VolStabW.FiniteThetaCoordinates.continuous_piW_inf (w : InfinitePlace F) :
    Continuous (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w : Ainf F → w.Completion) := by sorry
