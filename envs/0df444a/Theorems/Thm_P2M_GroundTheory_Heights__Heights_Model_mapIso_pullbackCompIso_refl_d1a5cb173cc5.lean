-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
-- name    : P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:36.436803+00:00
-- url     : https://prove2.me/theorems/6b153b32-00a8-497d-9fd0-0ec37b5b4549
-- title:
--   P2 M Ground Theory Heights  Heights Model map Iso pullback Comp Iso refl d1a5cb173cc5: P2 M Ground Theory Heights  Heights Model map Iso pullback Comp Iso refl d1a5cb173cc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model map Iso pullback Comp Iso refl d1a5cb173cc5 construction uses the P2 M Ground Theory Heights  Heights Model map Iso pullback Comp Iso refl d1a5cb173cc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L77-L85

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

theorem P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5 (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k')
    (e' : g' ≫ h = k') (E : Z.Modules) :
    (Scheme.Modules.pullback t).mapIso (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj E))) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' (Iso.refl _) ≪≫
        pullbackCompIso eg (Iso.refl _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mapIso_pullbackCompIso_refl» := P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
