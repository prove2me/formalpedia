-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:37.325021+00:00
-- url     : https://prove2.me/theorems/40883bcb-1cd3-5dc6-801c-dcfbe7826333
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul hom fa87e4e2089e: P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul hom fa87e4e2089e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul hom fa87e4e2089e construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists pull eq nsmul hom fa87e4e2089e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L45-L67

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    {U : X.Opens} (hU : IsAffineOpen U) {F G : (invOpen f a : Scheme.{0}).Modules}
    (φ : (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, (invOpen f a).ι ⁻¹ᵁ U)} {e' : Fin k' → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)}
    (he : IsBasisOn F _ e) (he' : IsBasisOn G _ e') :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U →
      ∀ s : Γ(F, V), ∃ τ : Γ(G, V), pullSectionOn (toInvOpen f ℚ a hq) G V τ =
        N • φ.app (toInvOpen f ℚ a hq ⁻¹ᵁ V) (pullSectionOn (toInvOpen f ℚ a hq) F V s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSections».«exists_pull_eq_nsmul_hom» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e
