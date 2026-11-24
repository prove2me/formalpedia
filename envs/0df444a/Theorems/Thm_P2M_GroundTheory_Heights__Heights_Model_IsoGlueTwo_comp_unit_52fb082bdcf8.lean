-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:14.869061+00:00
-- url     : https://prove2.me/theorems/25dde826-42ee-422a-829f-aeb6916965a4
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two comp unit 52fb082bdcf8: P2 M Ground Theory Heights  Heights Model Iso Glue Two comp unit 52fb082bdcf8
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two comp unit 52fb082bdcf8 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two comp unit 52fb082bdcf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L165-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
open Scheme.Modules GlueModulesStar
variable {X Z₁ Z₂ T : Scheme.{0}}
variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8 {Z : Scheme.{0}} (f : Z ⟶ X) {A B : X.Modules} (α : A ⟶ B) :
    α ≫ (pullbackPushforwardAdjunction f).unit.app B =
      (pullbackPushforwardAdjunction f).homEquiv _ _ ((Scheme.Modules.pullback f).map α) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«comp_unit» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8
