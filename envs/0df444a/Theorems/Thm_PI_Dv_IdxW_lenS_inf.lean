-- Prove2me | Theorems.Thm_PI_Dv_IdxW_lenS_inf
-- name    : PI.Dv.IdxW.lenS_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:54.386349+00:00
-- url     : https://prove2.me/theorems/385cd0f3-e34c-537f-91ca-faf740eaf370
-- title:
--   Idx W: len S inf
-- statement:
--   The Idx W construction uses the len S inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {V : Type*} [AddCommGroup V] [Module R V]

theorem PI.Dv.IdxW.lenS_inf (M N : Submodule R V) : lenS S M N = lenS S M (M ⊓ N) := by sorry
