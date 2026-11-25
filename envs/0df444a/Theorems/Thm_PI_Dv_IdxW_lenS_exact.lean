-- Prove2me | Theorems.Thm_PI_Dv_IdxW_lenS_exact
-- name    : PI.Dv.IdxW.lenS_exact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:15.093699+00:00
-- url     : https://prove2.me/theorems/f75fb47e-4aea-470e-ab87-90fa2599efe4
-- title:
--   Idx W: len S exact
-- statement:
--   The Idx W construction uses the len S exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L15-L23

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

theorem PI.Dv.IdxW.lenS_exact {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.length (Localization S) (LocalizedModule S B) =
      Module.length (Localization S) (LocalizedModule S A) +
        Module.length (Localization S) (LocalizedModule S C) := by sorry
