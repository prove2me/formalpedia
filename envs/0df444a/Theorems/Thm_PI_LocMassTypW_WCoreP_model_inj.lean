-- Prove2me | Theorems.Thm_PI_LocMassTypW_WCoreP_model_inj
-- name    : PI.LocMassTypW.WCoreP.model_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:48.300863+00:00
-- url     : https://prove2.me/theorems/373999d7-1b03-4788-b83d-fbb73c1d3c3c
-- title:
--   WCore P: model inj
-- statement:
--   The WCore P construction uses the model inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L9-L40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module

theorem PI.LocMassTypW.WCoreP.model_inj {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup Z] [Module K Z]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V) (T : Submodule K W) (ζ : Z →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w)
    (hT : ∀ w, b (a w) ∈ T → b (a w) = 0)
    (hζ : Function.Injective ζ) (hζb : ∀ z, b (ζ z) = 0)
    (hζa : ∀ z w, ζ z = a w → ζ z = 0) :
    Function.Injective (LinearMap.coprod a (LinearMap.coprod (s ∘ₗ T.subtype) ζ)) := by sorry
