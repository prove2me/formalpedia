-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:45.866731+00:00
-- url     : https://prove2.me/theorems/84b36cdd-1b71-41af-b649-ff842e9c4f44
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp Iso trans right 2820c52d5ef0: P2 M Ground Theory Heights  Heights Model pullback Comp Iso trans right 2820c52d5ef0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp Iso trans right 2820c52d5ef0 construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp Iso trans right 2820c52d5ef0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L17-L21

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0 {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F F' : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) (δ : F ≅ F') :
    pullbackCompIso e (γ ≪≫ δ) = pullbackCompIso e γ ≪≫ (Scheme.Modules.pullback g).mapIso δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackCompIso_trans_right» := P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0
