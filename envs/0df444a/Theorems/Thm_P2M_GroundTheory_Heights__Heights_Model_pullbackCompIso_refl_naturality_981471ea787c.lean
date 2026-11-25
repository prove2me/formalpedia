-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:14.708262+00:00
-- url     : https://prove2.me/theorems/e824a10f-f08a-4a76-94be-0efea66cc969
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp Iso refl naturality 981471ea787c: P2 M Ground Theory Heights  Heights Model pullback Comp Iso refl naturality 981471ea787c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp Iso refl naturality 981471ea787c construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp Iso refl naturality 981471ea787c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L87-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    {F F' : Y.Modules} (δ : F ≅ F') :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F)) ≪≫
        (Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullback g).mapIso δ) =
      (Scheme.Modules.pullback g').mapIso δ ≪≫ pullbackCompIso eg (Iso.refl _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackCompIso_refl_naturality» := P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c
