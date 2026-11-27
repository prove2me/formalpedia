-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_refl_4b91b8287c9c
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_refl_4b91b8287c9c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:38.626253+00:00
-- url     : https://prove2.me/theorems/3bae3545-e2bb-5bfa-8a22-ebc03b939433
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Iso Along refl 4b91b8287c9c: P2 M Ground Theory Heights  Heights Model pullback Iso Along refl 4b91b8287c9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Iso Along refl 4b91b8287c9c construction uses the P2 M Ground Theory Heights  Heights Model pullback Iso Along refl 4b91b8287c9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadGlue.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadGlue.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadIsoLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadGlue
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
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_refl_4b91b8287c9c {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) (F : Z.Modules) :
    pullbackIsoAlong e (Iso.refl ((Scheme.Modules.pullback h).obj F)) = Iso.refl _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackIsoAlong_refl» := P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_refl_4b91b8287c9c
