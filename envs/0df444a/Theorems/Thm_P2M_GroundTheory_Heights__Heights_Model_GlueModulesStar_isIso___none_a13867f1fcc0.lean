-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_a13867f1fcc0
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_a13867f1fcc0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:43.721443+00:00
-- url     : https://prove2.me/theorems/45535e2b-0fe8-4713-9706-53ddfa7e3fb7
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none a13867f1fcc0: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none a13867f1fcc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none a13867f1fcc0 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   none a13867f1fcc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L23-L37

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
variable {C : Type*} [Category C] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_a13867f1fcc0 {I : MulticospanIndex (starShape ι) C} {K : Multifork I} (hK : IsLimit K)
    (h : ∀ j, IsIso (I.snd j)) : IsIso (K.ι none) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_ι_none» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_a13867f1fcc0
