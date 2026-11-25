-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_piV_algebraMap
-- name    : PI.VolStabSW.FiniteThetaCoordinates.norm_piV_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:14.451363+00:00
-- url     : https://prove2.me/theorems/cda6540a-459e-5e2c-8039-fbba5f780db3
-- title:
--   Finite Theta Coordinates: norm pi V algebra Map
-- statement:
--   The Finite Theta Coordinates construction uses the norm pi V algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L166-L169

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

theorem PI.VolStabSW.FiniteThetaCoordinates.norm_piV_algebraMap (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖piV F v (algebraMap F (AF F) x)‖ = ‖FinitePlace.embedding v x‖ := by sorry
