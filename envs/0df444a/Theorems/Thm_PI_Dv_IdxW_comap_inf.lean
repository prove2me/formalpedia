-- Prove2me | Theorems.Thm_PI_Dv_IdxW_comap_inf
-- name    : PI.Dv.IdxW.comap_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:21.57433+00:00
-- url     : https://prove2.me/theorems/b23af231-e65e-5fd6-837b-41b80a3117dd
-- title:
--   Idx W: comap inf
-- statement:
--   The Idx W construction uses the comap inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L30-L33

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

theorem PI.Dv.IdxW.comap_inf (M N : Submodule R V) : N.comap M.subtype = (M ⊓ N).comap M.subtype := by sorry
