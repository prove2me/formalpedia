-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:18.568454+00:00
-- url     : https://prove2.me/theorems/05be497c-a203-4047-b06b-75f2ba498b05
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some f8685ded3020: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some f8685ded3020
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some f8685ded3020 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso   some f8685ded3020 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L39-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L39-L67

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

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020 [DecidableEq ι] {I : MulticospanIndex (starShape ι) C} {K : Multifork I}
    (hK : IsLimit K) (i : ι) (hi : IsIso (I.fst i)) (h : ∀ j, j ≠ i → IsIso (I.snd j)) :
    IsIso (K.ι (some i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_ι_some» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020
