-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:19.595836+00:00
-- url     : https://prove2.me/theorems/97907f66-7d90-48c8-acbd-80d9d1e2d36c
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul hom 3ff6d176c247: P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul hom 3ff6
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul hom 3ff6d176c247 construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul hom 3ff6d176c247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L57-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L57-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
variable {Y T : Scheme.{0}} (π : T ⟶ Y) (p : ℕ)

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247 (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, W)} {e' : Fin k' → Γ(G, W)}
    (he : IsBasisOn F W e) (he' : IsBasisOn G W e') :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∀ V : Y.Opens, V ≤ W → ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
      pullSectionOn π G V τ = N • φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSectionsLoc».«exists_pull_eq_nsmul_hom» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247
