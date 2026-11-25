-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:21.805259+00:00
-- url     : https://prove2.me/theorems/3321c385-52bf-4fd8-9035-a97f7ab373bd
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom hom eq of pull Section On 65c3ce803d1f: P2 M Ground Theory Heights  Heights Model Descend Hom hom eq of pull Section On 65c3ce803d1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom hom eq of pull Section On 65c3ce803d1f construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom hom eq of pull Section On 65c3ce803d1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L69-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
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
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f (g : T ⟶ Y) (R : Y.Opens) (hR : g ⁻¹ᵁ R = ⊤) {F G : Y.Modules}
    (χ₁ χ₂ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (h : ∀ V : Y.Opens, V ≤ R → ∀ s : Γ(F, V),
      χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) :
    χ₁ = χ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«hom_eq_of_pullSectionOn» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f
