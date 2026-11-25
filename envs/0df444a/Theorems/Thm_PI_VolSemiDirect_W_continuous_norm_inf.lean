-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_continuous_norm_inf
-- name    : PI.VolSemiDirect.W.continuous_norm_inf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:36.194386+00:00
-- url     : https://prove2.me/theorems/eb4c1a57-3a46-4cdb-b4e7-4214f015c120
-- title:
--   W: continuous norm inf
-- statement:
--   The W construction uses the continuous norm inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolSemiDirect.W.continuous_norm_inf : Continuous fun y : InfiniteAdeleRing F => ‖y‖ := by sorry
