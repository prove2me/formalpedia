-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:31.63778+00:00
-- url     : https://prove2.me/theorems/0843cffa-4457-5b39-aa28-77068125977f
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul 8f51e6cf42cb: P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul 8f51e6cf42cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul 8f51e6cf42cb construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul 8f51e6cf42cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L29-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsRatDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSections
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
open GroundTheory.Heights₂.Heights.Model.SpreadHomSections
variable {X : Scheme.{0}} (f : X ⟶ SpecZ) (a : ℤ) (hq : IsUnit (a : ℚ))

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    {U : X.Opens} (hU : IsAffineOpen U) {G : (invOpen f a : Scheme.{0}).Modules} {k : ℕ}
    {e : Fin k → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)} (he : IsBasisOn G _ e)
    (σ : Γ((Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G,
      toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(G, (invOpen f a).ι ⁻¹ᵁ U),
      pullSectionOn (toInvOpen f ℚ a hq) G _ τ = N • σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSections».«exists_pull_eq_nsmul» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb
