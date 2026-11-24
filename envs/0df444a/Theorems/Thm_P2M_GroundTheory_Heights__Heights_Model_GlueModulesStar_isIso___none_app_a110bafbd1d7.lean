-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:48.585191+00:00
-- url     : https://prove2.me/theorems/92a7b186-eda6-47ee-87c3-24ce49457d1b
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none app a110bafbd1d7: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none app a110bafbd1d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none app a110bafbd1d7 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none app a110bafbd1d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L183-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L183-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
variable {X : Scheme.{u}} (V : X.Opens) {ι : Type u} (U : ι → X.Opens)
  (G : (V : Scheme.{u}).Modules) (F : ∀ i, (U i : Scheme.{u}).Modules)
  (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
    (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)
set_option backward.isDefEq.respectTransparency false

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7 (W : X.Opens) (hW : W ≤ V) :
    IsIso ((Multiequalizer.ι (index V U G F ψ) none).app W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_ι_none_app» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7
