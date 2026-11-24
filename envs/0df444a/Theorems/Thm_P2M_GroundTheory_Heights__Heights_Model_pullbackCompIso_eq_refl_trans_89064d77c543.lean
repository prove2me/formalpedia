-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:14.381781+00:00
-- url     : https://prove2.me/theorems/0c541f25-1646-45e7-82ef-d84e4f82dacb
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Comp Iso eq refl trans 89064d77c543: P2 M Ground Theory Heights  Heights Model pullback Comp Iso eq refl trans 89064d77c543
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Comp Iso eq refl trans 89064d77c543 construction uses the P2 M Ground Theory Heights  Heights Model pullback Comp Iso eq refl trans 89064d77c543 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean#L23-L26

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543 {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e γ = pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso γ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackCompIso_eq_refl_trans» := P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
