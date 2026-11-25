-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:11.56681+00:00
-- url     : https://prove2.me/theorems/f67c4ad9-2129-49e6-a762-931906df65ff
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul 3fd3275048f4: P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul 3fd3275048f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul 3fd3275048f4 construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists pull eq nsmul 3fd3275048f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L41-L55

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4 (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {G : Y.Modules} {k : ℕ} {e : Fin k → Γ(G, W)} (he : IsBasisOn G W e)
    (σ : Γ((Scheme.Modules.pullback π).obj G, π ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ τ : Γ(G, W), pullSectionOn π G W τ = N • σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSectionsLoc».«exists_pull_eq_nsmul» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4
