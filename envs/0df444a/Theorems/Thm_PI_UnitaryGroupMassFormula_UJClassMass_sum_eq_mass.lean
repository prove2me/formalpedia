-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sum_eq_mass
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.sum_eq_mass
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:25.948556+00:00
-- url     : https://prove2.me/theorems/515ca50c-721b-42f4-886c-3219be9cff82
-- title:
--   UJClass Mass: sum eq mass
-- statement:
--   The UJClass Mass construction uses the sum eq mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/Reduce.lean#L100-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/Reduce.lean#L100-L136

import Definitions.Def_Formalism_PeriodIntegrals_UJClassMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)
variable {Γ Kf h L0}

theorem PI.UnitaryGroupMassFormula.UJClassMass.sum_eq_mass {Λ : G → Submodule (𝓞 K) V} {ι : Γ → V ≃ₗ[K] V} (D : IsDict Γ Kf h L0 Λ ι)
    (n : ℕ) (g : Fin n → G)
    (hcov : ∀ x, ∃ i, ∃ γ : Γ, ∃ k : Kf, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : Kf), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) :
    ∑ i, ((Nat.card (PI.UJClassMass.stab Γ Kf (g i)) : ℝ))⁻¹ = mass h L0 := by sorry
