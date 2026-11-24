-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:40.895865+00:00
-- url     : https://prove2.me/theorems/0c827068-fd93-4fdc-a88e-7a0e5646df67
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp  3ff0e312897d: P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp  3ff0e312897d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp  3ff0e312897d construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp  3ff0e312897d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L68-L75

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (Iso.refl _) ≪≫
      (Scheme.Modules.pullback t).mapIso (pullbackCompIso e γ) ≪≫
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackCompIso_comp'» := P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
