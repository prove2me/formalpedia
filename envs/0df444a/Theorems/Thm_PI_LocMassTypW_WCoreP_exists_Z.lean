-- Prove2me | Theorems.Thm_PI_LocMassTypW_WCoreP_exists_Z
-- name    : PI.LocMassTypW.WCoreP.exists_Z
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:35.651852+00:00
-- url     : https://prove2.me/theorems/f4c47f1e-8c25-4a81-95ae-52dfe25d25a8
-- title:
--   WCore P: exists Z
-- statement:
--   The WCore P construction uses the exists Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L42-L70

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

theorem PI.LocMassTypW.WCoreP.exists_Z {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w) :
    ∃ Z : Submodule K V, Z ≤ LinearMap.ker b ∧ (∀ z ∈ Z, z ∈ LinearMap.range a → z = 0) ∧
      finrank K Z + finrank K (LinearMap.ker (b ∘ₗ a)) + finrank K W = finrank K V := by sorry
