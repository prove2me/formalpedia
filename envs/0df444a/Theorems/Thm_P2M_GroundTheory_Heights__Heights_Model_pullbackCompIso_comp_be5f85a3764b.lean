-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:20.070577+00:00
-- url     : https://prove2.me/theorems/3b0291e8-c100-4b88-849e-34855a5345dc
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp be5f85a3764b: P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp be5f85a3764b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp be5f85a3764b construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp Iso comp be5f85a3764b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L28-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L28-L58

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (pullbackCompIso e γ) ≪≫
      (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackCompIso_comp» := P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b
