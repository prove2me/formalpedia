-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:53.459799+00:00
-- url     : https://prove2.me/theorems/c4cc7eaa-1a64-4365-a7ee-bbbe7981a61b
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc main de3e7704d2b0: P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc main de3e7704d2b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc main de3e7704d2b0 construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc main de3e7704d2b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L80-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L80-L154

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0 (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) (fY : Y ⟶ SpecZ) [CompactSpace Y]
    (hden : ∀ W : Y.Opens, IsAffineOpen W → ∀ b : Γ(T, π ⁻¹ᵁ W),
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (hF : IsVectorBundle F) (hG : IsVectorBundle G)
    (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hpm₀ : ¬ p ∣ m₀)
    (hinj : ∀ n : ℕ, 0 < n → m₀ ∣ n → ¬ p ∣ n → ∀ V : Y.Opens, V ≤ invOpen fY n →
      Function.Injective (pullSectionOn π G V)) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ p ∣ n →
      ∀ V : Y.Opens, V ≤ invOpen fY n → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
        pullSectionOn π G V t = φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSectionsLoc».«main» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0
