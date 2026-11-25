-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:43.871207+00:00
-- url     : https://prove2.me/theorems/7af2fd03-9bc7-4aab-bfc5-8dde3360a464
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some app a44c38561947: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some app a44c38561947
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some app a44c38561947 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some app a44c38561947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L200-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L200-L218

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

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947 (hUU : ∀ i j, i ≠ j → U i ⊓ U j ≤ V) (i : ι) (W : X.Opens)
    (hW : W ≤ U i) : IsIso ((Multiequalizer.ι (index V U G F ψ) (some i)).app W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_ι_some_app» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947
