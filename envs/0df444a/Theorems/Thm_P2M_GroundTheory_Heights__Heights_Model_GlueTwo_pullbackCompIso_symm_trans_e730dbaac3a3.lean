-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:22.649164+00:00
-- url     : https://prove2.me/theorems/878d3686-cbe3-583d-9044-210ea48f4d4c
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Two pullback Comp Iso symm trans e730dbaac3a3: P2 M Ground Theory Heights  Heights Model Glue Two pullback Comp Iso symm trans e730dbaac3a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Two pullback Comp Iso symm trans e730dbaac3a3 construction uses the P2 M Ground Theory Heights  Heights Model Glue Two pullback Comp Iso symm trans e730dbaac3a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueTwo.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueTwo.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueTwo
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
open GroundTheory.Heights₂.Heights.Model.GlueTwo

theorem P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3 {A B C Z : Scheme.{0}} {t : A ⟶ B} {s : B ⟶ C} {ι : C ⟶ Z}
    {j : B ⟶ Z} {u : A ⟶ C} {w : A ⟶ Z} (e : s ≫ ι = j) (eg : t ≫ s = u) (ek : t ≫ j = w)
    (e' : u ≫ ι = w) {E : Z.Modules} {F : B.Modules} (a : (Scheme.Modules.pullback j).obj E ≅ F) :
    pullbackCompIso eg ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a) =
      (pullbackCompIso e' (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫
        pullbackCompIso ek a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueTwo».«pullbackCompIso_symm_trans» := P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3
