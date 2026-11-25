-- Prove2me | Theorems.Thm_PI_Dv_GLP_isIntegral_trace_of_pow
-- name    : PI.Dv.GLP.isIntegral_trace_of_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:35.386269+00:00
-- url     : https://prove2.me/theorems/7e7dce82-b41f-4df6-a580-25b6a7beec30
-- title:
--   GLP: is Integral trace of pow
-- statement:
--   The GLP construction uses the is Integral trace of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/IsIntegralTraceOfPow.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/IsIntegralTraceOfPow.lean#L15-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ArithmeticCylinders
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_IsIntegralTraceOfPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Polynomial

theorem PI.Dv.GLP.isIntegral_trace_of_pow {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace K W f) := by sorry
