-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:36.312315+00:00
-- url     : https://prove2.me/theorems/247eb346-acf7-45e7-bf4f-e97f0c585743
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp trans congr 76dd066c1c0a: P2 M Ground Theory Heights  Heights Model pullback Comp trans congr 76dd066c1c0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp trans congr 76dd066c1c0a construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp trans congr 76dd066c1c0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L60-L66

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    (F : Y.Modules) :
    (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F =
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackComp_trans_congr» := P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a
