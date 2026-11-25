-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:13.671848+00:00
-- url     : https://prove2.me/theorems/8d7af4de-6662-4d23-b1b3-3562c2c42951
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom descend Psi pull fbe1ad794e99: P2 M Ground Theory Heights  Heights Model Descend Hom descend Psi pull fbe1ad794e99
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom descend Psi pull fbe1ad794e99 construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom descend Psi pull fbe1ad794e99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L148-L155

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
variable {T Y Z : Scheme.{0}} (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) {F G : Y.Modules}
  (φ : (Scheme.Modules.pullback (g' ≫ ι)).obj F ⟶ (Scheme.Modules.pullback (g' ≫ ι)).obj G)
  (hinj : ∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn (g' ≫ ι) G V))
  (t : ∀ V : Y.Opens, V ≤ ι.opensRange → Γ(F, V) → Γ(G, V))
  (ht : ∀ (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)),
    pullSectionOn (g' ≫ ι) G V (t V hV s) =
      φ.app ((g' ≫ ι) ⁻¹ᵁ V) (pullSectionOn (g' ≫ ι) F V s))
include hinj ht

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99 (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)) :
    (descendPsi ι g' φ hinj t ht).app (ι ⁻¹ᵁ V) (pullSectionOn ι F V s) =
      pullSectionOn ι G V (t V hV s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«descendPsi_pull» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99
