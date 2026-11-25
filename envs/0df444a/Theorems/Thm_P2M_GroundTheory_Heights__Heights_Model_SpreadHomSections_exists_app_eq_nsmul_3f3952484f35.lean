-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:50.508556+00:00
-- url     : https://prove2.me/theorems/7c412d38-2b52-4305-aa02-dd595a906228
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists app eq nsmul 3f3952484f35: P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists app eq nsmul 3f3952484f35
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists app eq nsmul 3f3952484f35 construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections exists app eq nsmul 3f3952484f35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSections.lean#L20-L27

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35 (h₁ : RatDenominators.Statement) {U : X.Opens} (hU : IsAffineOpen U)
    (b : Γ(baseChange f ℚ, toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : Γ((invOpen f a : Scheme.{0}), (invOpen f a).ι ⁻¹ᵁ U),
      (toInvOpen f ℚ a hq).app _ c = N • b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSections».«exists_app_eq_nsmul» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35
